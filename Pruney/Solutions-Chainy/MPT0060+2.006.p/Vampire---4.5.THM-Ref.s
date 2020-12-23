%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:14 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   31 (  49 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   32 (  50 expanded)
%              Number of equality atoms :   31 (  49 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f163,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f163,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f155,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f155,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f139,f18])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f17,f15])).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f13,f13])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f139,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1) ),
    inference(superposition,[],[f11,f118])).

fof(f118,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(k3_xboole_0(X3,X5),X4) ),
    inference(forward_demodulation,[],[f117,f84])).

fof(f84,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k2_xboole_0(X4,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f25,f12])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f16,f13])).

fof(f117,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X5))) ),
    inference(backward_demodulation,[],[f37,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f30,f12])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f14,f16])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f37,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f28,f16])).

fof(f28,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5))) ),
    inference(superposition,[],[f16,f13])).

fof(f11,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (721256449)
% 0.14/0.37  ipcrm: permission denied for id (721289218)
% 0.14/0.37  ipcrm: permission denied for id (722632707)
% 0.14/0.37  ipcrm: permission denied for id (726368260)
% 0.14/0.37  ipcrm: permission denied for id (721321989)
% 0.14/0.37  ipcrm: permission denied for id (721354758)
% 0.14/0.37  ipcrm: permission denied for id (721387527)
% 0.14/0.37  ipcrm: permission denied for id (728498184)
% 0.14/0.38  ipcrm: permission denied for id (721420297)
% 0.14/0.38  ipcrm: permission denied for id (728530954)
% 0.14/0.38  ipcrm: permission denied for id (728563723)
% 0.14/0.38  ipcrm: permission denied for id (722796556)
% 0.20/0.38  ipcrm: permission denied for id (728596493)
% 0.20/0.38  ipcrm: permission denied for id (726532110)
% 0.20/0.38  ipcrm: permission denied for id (722894863)
% 0.20/0.38  ipcrm: permission denied for id (726564880)
% 0.20/0.39  ipcrm: permission denied for id (722960401)
% 0.20/0.39  ipcrm: permission denied for id (726597650)
% 0.20/0.39  ipcrm: permission denied for id (723025939)
% 0.20/0.39  ipcrm: permission denied for id (723058708)
% 0.20/0.39  ipcrm: permission denied for id (723091477)
% 0.20/0.39  ipcrm: permission denied for id (726630422)
% 0.20/0.39  ipcrm: permission denied for id (723157015)
% 0.20/0.39  ipcrm: permission denied for id (723189784)
% 0.20/0.40  ipcrm: permission denied for id (723222553)
% 0.20/0.40  ipcrm: permission denied for id (726663194)
% 0.20/0.40  ipcrm: permission denied for id (726695963)
% 0.20/0.40  ipcrm: permission denied for id (726761501)
% 0.20/0.40  ipcrm: permission denied for id (723386398)
% 0.20/0.40  ipcrm: permission denied for id (721518623)
% 0.20/0.40  ipcrm: permission denied for id (721551392)
% 0.20/0.41  ipcrm: permission denied for id (721584161)
% 0.20/0.41  ipcrm: permission denied for id (726794274)
% 0.20/0.41  ipcrm: permission denied for id (721616931)
% 0.20/0.41  ipcrm: permission denied for id (723451940)
% 0.20/0.41  ipcrm: permission denied for id (726827045)
% 0.20/0.41  ipcrm: permission denied for id (721682470)
% 0.20/0.41  ipcrm: permission denied for id (723517479)
% 0.20/0.42  ipcrm: permission denied for id (729317416)
% 0.20/0.42  ipcrm: permission denied for id (729350185)
% 0.20/0.42  ipcrm: permission denied for id (729382954)
% 0.20/0.42  ipcrm: permission denied for id (723681323)
% 0.20/0.42  ipcrm: permission denied for id (723714092)
% 0.20/0.42  ipcrm: permission denied for id (723779629)
% 0.20/0.42  ipcrm: permission denied for id (727056430)
% 0.20/0.42  ipcrm: permission denied for id (728793135)
% 0.20/0.42  ipcrm: permission denied for id (728825904)
% 0.20/0.42  ipcrm: permission denied for id (727154737)
% 0.20/0.43  ipcrm: permission denied for id (727187506)
% 0.20/0.43  ipcrm: permission denied for id (727220275)
% 0.20/0.43  ipcrm: permission denied for id (724009012)
% 0.20/0.43  ipcrm: permission denied for id (724041781)
% 0.20/0.43  ipcrm: permission denied for id (721846326)
% 0.20/0.43  ipcrm: permission denied for id (724074551)
% 0.20/0.43  ipcrm: permission denied for id (727253048)
% 0.20/0.43  ipcrm: permission denied for id (727285817)
% 0.20/0.44  ipcrm: permission denied for id (724172858)
% 0.20/0.44  ipcrm: permission denied for id (724205627)
% 0.20/0.44  ipcrm: permission denied for id (724271165)
% 0.20/0.44  ipcrm: permission denied for id (729448510)
% 0.20/0.44  ipcrm: permission denied for id (727384127)
% 0.20/0.44  ipcrm: permission denied for id (727416896)
% 0.20/0.44  ipcrm: permission denied for id (728924225)
% 0.20/0.44  ipcrm: permission denied for id (727482434)
% 0.20/0.45  ipcrm: permission denied for id (724467779)
% 0.20/0.45  ipcrm: permission denied for id (727515204)
% 0.20/0.45  ipcrm: permission denied for id (724533317)
% 0.20/0.45  ipcrm: permission denied for id (727547974)
% 0.20/0.45  ipcrm: permission denied for id (724598855)
% 0.20/0.45  ipcrm: permission denied for id (727580744)
% 0.20/0.45  ipcrm: permission denied for id (724664393)
% 0.20/0.45  ipcrm: permission denied for id (724697162)
% 0.20/0.45  ipcrm: permission denied for id (724729931)
% 0.20/0.45  ipcrm: permission denied for id (727613516)
% 0.20/0.46  ipcrm: permission denied for id (724795469)
% 0.20/0.46  ipcrm: permission denied for id (724828238)
% 0.20/0.46  ipcrm: permission denied for id (727646287)
% 0.20/0.46  ipcrm: permission denied for id (724893776)
% 0.20/0.46  ipcrm: permission denied for id (727679057)
% 0.20/0.46  ipcrm: permission denied for id (727711826)
% 0.20/0.46  ipcrm: permission denied for id (724992083)
% 0.20/0.46  ipcrm: permission denied for id (727744596)
% 0.20/0.46  ipcrm: permission denied for id (727777365)
% 0.20/0.47  ipcrm: permission denied for id (725090390)
% 0.20/0.47  ipcrm: permission denied for id (729776215)
% 0.20/0.47  ipcrm: permission denied for id (727842904)
% 0.20/0.47  ipcrm: permission denied for id (725188697)
% 0.20/0.47  ipcrm: permission denied for id (727875674)
% 0.20/0.47  ipcrm: permission denied for id (728989787)
% 0.20/0.47  ipcrm: permission denied for id (729808988)
% 0.20/0.47  ipcrm: permission denied for id (725319773)
% 0.20/0.47  ipcrm: permission denied for id (729546846)
% 0.20/0.48  ipcrm: permission denied for id (725385311)
% 0.20/0.48  ipcrm: permission denied for id (729088096)
% 0.20/0.48  ipcrm: permission denied for id (725450849)
% 0.20/0.48  ipcrm: permission denied for id (722141282)
% 0.20/0.48  ipcrm: permission denied for id (722174051)
% 0.20/0.48  ipcrm: permission denied for id (728039524)
% 0.20/0.48  ipcrm: permission denied for id (722206821)
% 0.20/0.48  ipcrm: permission denied for id (725516390)
% 0.20/0.48  ipcrm: permission denied for id (725549159)
% 0.20/0.48  ipcrm: permission denied for id (725581928)
% 0.20/0.49  ipcrm: permission denied for id (728105066)
% 0.20/0.49  ipcrm: permission denied for id (722272363)
% 0.20/0.49  ipcrm: permission denied for id (729153644)
% 0.20/0.49  ipcrm: permission denied for id (729874541)
% 0.20/0.49  ipcrm: permission denied for id (728203374)
% 0.20/0.49  ipcrm: permission denied for id (722337903)
% 0.20/0.49  ipcrm: permission denied for id (725811312)
% 0.20/0.49  ipcrm: permission denied for id (722370673)
% 0.20/0.49  ipcrm: permission denied for id (728268914)
% 0.20/0.50  ipcrm: permission denied for id (725876851)
% 0.20/0.50  ipcrm: permission denied for id (725909620)
% 0.20/0.50  ipcrm: permission denied for id (725942389)
% 0.20/0.50  ipcrm: permission denied for id (726007926)
% 0.20/0.50  ipcrm: permission denied for id (722436215)
% 0.20/0.50  ipcrm: permission denied for id (726073464)
% 0.20/0.50  ipcrm: permission denied for id (726106233)
% 0.20/0.50  ipcrm: permission denied for id (728301690)
% 0.20/0.50  ipcrm: permission denied for id (729645179)
% 0.20/0.50  ipcrm: permission denied for id (728367228)
% 0.20/0.50  ipcrm: permission denied for id (728399997)
% 0.20/0.51  ipcrm: permission denied for id (726270078)
% 0.20/0.51  ipcrm: permission denied for id (728432767)
% 0.69/0.60  % (25390)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.69/0.60  % (25391)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.69/0.62  % (25389)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.69/0.62  % (25401)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.69/0.62  % (25392)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.69/0.62  % (25400)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.69/0.62  % (25389)Refutation found. Thanks to Tanya!
% 0.69/0.62  % SZS status Theorem for theBenchmark
% 0.69/0.62  % SZS output start Proof for theBenchmark
% 0.69/0.62  fof(f165,plain,(
% 0.69/0.62    $false),
% 0.69/0.62    inference(trivial_inequality_removal,[],[f164])).
% 0.69/0.62  fof(f164,plain,(
% 0.69/0.62    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.69/0.62    inference(forward_demodulation,[],[f163,f12])).
% 0.69/0.62  fof(f12,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f1])).
% 0.69/0.62  fof(f1,axiom,(
% 0.69/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.69/0.62  fof(f163,plain,(
% 0.69/0.62    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 0.69/0.62    inference(superposition,[],[f155,f16])).
% 0.69/0.62  fof(f16,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.69/0.62    inference(cnf_transformation,[],[f3])).
% 0.69/0.62  fof(f3,axiom,(
% 0.69/0.62    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.69/0.62  fof(f155,plain,(
% 0.69/0.62    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.69/0.62    inference(forward_demodulation,[],[f139,f18])).
% 0.69/0.62  fof(f18,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.69/0.62    inference(forward_demodulation,[],[f17,f15])).
% 0.69/0.62  fof(f15,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.69/0.62    inference(cnf_transformation,[],[f4])).
% 0.69/0.62  fof(f4,axiom,(
% 0.69/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.69/0.62  fof(f17,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.69/0.62    inference(superposition,[],[f13,f13])).
% 0.69/0.62  fof(f13,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.69/0.62    inference(cnf_transformation,[],[f5])).
% 0.69/0.62  fof(f5,axiom,(
% 0.69/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.69/0.62  fof(f139,plain,(
% 0.69/0.62    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1)),
% 0.69/0.62    inference(superposition,[],[f11,f118])).
% 0.69/0.62  fof(f118,plain,(
% 0.69/0.62    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(k3_xboole_0(X3,X5),X4)) )),
% 0.69/0.62    inference(forward_demodulation,[],[f117,f84])).
% 0.69/0.62  fof(f84,plain,(
% 0.69/0.62    ( ! [X4,X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k2_xboole_0(X4,k4_xboole_0(X2,X3)))) )),
% 0.69/0.62    inference(superposition,[],[f25,f12])).
% 0.69/0.62  fof(f25,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.69/0.62    inference(superposition,[],[f16,f13])).
% 0.69/0.62  fof(f117,plain,(
% 0.69/0.62    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X5)))) )),
% 0.69/0.62    inference(backward_demodulation,[],[f37,f108])).
% 0.69/0.62  fof(f108,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))) )),
% 0.69/0.62    inference(superposition,[],[f30,f12])).
% 0.69/0.62  fof(f30,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 0.69/0.62    inference(superposition,[],[f14,f16])).
% 0.69/0.62  fof(f14,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.69/0.62    inference(cnf_transformation,[],[f2])).
% 0.69/0.62  fof(f2,axiom,(
% 0.69/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.69/0.62  fof(f37,plain,(
% 0.69/0.62    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))) )),
% 0.69/0.62    inference(forward_demodulation,[],[f28,f16])).
% 0.69/0.62  fof(f28,plain,(
% 0.69/0.62    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5)))) )),
% 0.69/0.62    inference(superposition,[],[f16,f13])).
% 0.69/0.62  fof(f11,plain,(
% 0.69/0.62    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.69/0.62    inference(cnf_transformation,[],[f10])).
% 0.69/0.62  fof(f10,plain,(
% 0.69/0.62    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.69/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 0.69/0.62  fof(f9,plain,(
% 0.69/0.62    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.69/0.62    introduced(choice_axiom,[])).
% 0.69/0.62  fof(f8,plain,(
% 0.69/0.62    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.69/0.62    inference(ennf_transformation,[],[f7])).
% 0.69/0.62  fof(f7,negated_conjecture,(
% 0.69/0.62    ~! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.69/0.62    inference(negated_conjecture,[],[f6])).
% 0.69/0.62  fof(f6,conjecture,(
% 0.69/0.62    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 0.69/0.62  % SZS output end Proof for theBenchmark
% 0.69/0.62  % (25389)------------------------------
% 0.69/0.62  % (25389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.69/0.62  % (25389)Termination reason: Refutation
% 0.69/0.62  
% 0.69/0.62  % (25389)Memory used [KB]: 1791
% 0.69/0.62  % (25389)Time elapsed: 0.058 s
% 0.69/0.62  % (25389)------------------------------
% 0.69/0.62  % (25389)------------------------------
% 0.69/0.62  % (25228)Success in time 0.267 s
%------------------------------------------------------------------------------
