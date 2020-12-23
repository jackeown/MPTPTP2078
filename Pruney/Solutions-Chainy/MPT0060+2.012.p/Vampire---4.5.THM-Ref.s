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

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f872,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f855])).

fof(f855,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f108,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f108,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f94,f47])).

fof(f47,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f39,f14])).

fof(f14,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f39,plain,(
    ! [X6,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0) ),
    inference(superposition,[],[f16,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f18,f15])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f94,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2) ),
    inference(superposition,[],[f13,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f13,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:37:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (721256449)
% 0.21/0.37  ipcrm: permission denied for id (721289218)
% 0.21/0.37  ipcrm: permission denied for id (722632707)
% 0.21/0.37  ipcrm: permission denied for id (726368260)
% 0.21/0.37  ipcrm: permission denied for id (721321989)
% 0.21/0.38  ipcrm: permission denied for id (721354758)
% 0.21/0.38  ipcrm: permission denied for id (721387527)
% 0.21/0.38  ipcrm: permission denied for id (728498184)
% 0.21/0.38  ipcrm: permission denied for id (721420297)
% 0.21/0.38  ipcrm: permission denied for id (728530954)
% 0.21/0.38  ipcrm: permission denied for id (728563723)
% 0.21/0.38  ipcrm: permission denied for id (722796556)
% 0.21/0.38  ipcrm: permission denied for id (728596493)
% 0.21/0.39  ipcrm: permission denied for id (726532110)
% 0.21/0.39  ipcrm: permission denied for id (722894863)
% 0.21/0.39  ipcrm: permission denied for id (726564880)
% 0.21/0.39  ipcrm: permission denied for id (722960401)
% 0.21/0.39  ipcrm: permission denied for id (726597650)
% 0.21/0.39  ipcrm: permission denied for id (723025939)
% 0.21/0.39  ipcrm: permission denied for id (723058708)
% 0.21/0.39  ipcrm: permission denied for id (723091477)
% 0.21/0.40  ipcrm: permission denied for id (726630422)
% 0.21/0.40  ipcrm: permission denied for id (723157015)
% 0.21/0.40  ipcrm: permission denied for id (723189784)
% 0.21/0.40  ipcrm: permission denied for id (723222553)
% 0.21/0.40  ipcrm: permission denied for id (726663194)
% 0.21/0.40  ipcrm: permission denied for id (726695963)
% 0.21/0.40  ipcrm: permission denied for id (726761501)
% 0.21/0.40  ipcrm: permission denied for id (723386398)
% 0.21/0.41  ipcrm: permission denied for id (721518623)
% 0.21/0.41  ipcrm: permission denied for id (721551392)
% 0.21/0.41  ipcrm: permission denied for id (721584161)
% 0.21/0.41  ipcrm: permission denied for id (726794274)
% 0.21/0.41  ipcrm: permission denied for id (721616931)
% 0.21/0.41  ipcrm: permission denied for id (723451940)
% 0.21/0.41  ipcrm: permission denied for id (726827045)
% 0.21/0.41  ipcrm: permission denied for id (721682470)
% 0.21/0.42  ipcrm: permission denied for id (723517479)
% 0.21/0.42  ipcrm: permission denied for id (723681323)
% 0.21/0.42  ipcrm: permission denied for id (723714092)
% 0.21/0.42  ipcrm: permission denied for id (723779629)
% 0.21/0.42  ipcrm: permission denied for id (727056430)
% 0.21/0.42  ipcrm: permission denied for id (728793135)
% 0.21/0.43  ipcrm: permission denied for id (728825904)
% 0.21/0.43  ipcrm: permission denied for id (727154737)
% 0.21/0.43  ipcrm: permission denied for id (727187506)
% 0.21/0.43  ipcrm: permission denied for id (727220275)
% 0.21/0.43  ipcrm: permission denied for id (724009012)
% 0.21/0.43  ipcrm: permission denied for id (724041781)
% 0.21/0.43  ipcrm: permission denied for id (721846326)
% 0.21/0.43  ipcrm: permission denied for id (724074551)
% 0.21/0.44  ipcrm: permission denied for id (727253048)
% 0.21/0.44  ipcrm: permission denied for id (727285817)
% 0.21/0.44  ipcrm: permission denied for id (724172858)
% 0.21/0.44  ipcrm: permission denied for id (724205627)
% 0.21/0.44  ipcrm: permission denied for id (724271165)
% 0.21/0.44  ipcrm: permission denied for id (727384127)
% 0.21/0.45  ipcrm: permission denied for id (727416896)
% 0.21/0.45  ipcrm: permission denied for id (728924225)
% 0.21/0.45  ipcrm: permission denied for id (727482434)
% 0.21/0.45  ipcrm: permission denied for id (724467779)
% 0.21/0.45  ipcrm: permission denied for id (727515204)
% 0.21/0.45  ipcrm: permission denied for id (724533317)
% 0.21/0.45  ipcrm: permission denied for id (727547974)
% 0.21/0.45  ipcrm: permission denied for id (724598855)
% 0.21/0.46  ipcrm: permission denied for id (727580744)
% 0.21/0.46  ipcrm: permission denied for id (724664393)
% 0.21/0.46  ipcrm: permission denied for id (724697162)
% 0.21/0.46  ipcrm: permission denied for id (724729931)
% 0.21/0.46  ipcrm: permission denied for id (727613516)
% 0.21/0.46  ipcrm: permission denied for id (724795469)
% 0.21/0.46  ipcrm: permission denied for id (724828238)
% 0.21/0.46  ipcrm: permission denied for id (727646287)
% 0.21/0.46  ipcrm: permission denied for id (724893776)
% 0.21/0.47  ipcrm: permission denied for id (727679057)
% 0.21/0.47  ipcrm: permission denied for id (727711826)
% 0.21/0.47  ipcrm: permission denied for id (724992083)
% 0.21/0.47  ipcrm: permission denied for id (727744596)
% 0.21/0.47  ipcrm: permission denied for id (727777365)
% 0.21/0.47  ipcrm: permission denied for id (725090390)
% 0.21/0.47  ipcrm: permission denied for id (727842904)
% 0.21/0.48  ipcrm: permission denied for id (725188697)
% 0.21/0.48  ipcrm: permission denied for id (727875674)
% 0.21/0.48  ipcrm: permission denied for id (728989787)
% 0.21/0.48  ipcrm: permission denied for id (725319773)
% 0.21/0.48  ipcrm: permission denied for id (725385311)
% 0.21/0.48  ipcrm: permission denied for id (729088096)
% 0.21/0.49  ipcrm: permission denied for id (725450849)
% 0.21/0.49  ipcrm: permission denied for id (722141282)
% 0.21/0.49  ipcrm: permission denied for id (722174051)
% 0.21/0.49  ipcrm: permission denied for id (728039524)
% 0.21/0.49  ipcrm: permission denied for id (722206821)
% 0.21/0.49  ipcrm: permission denied for id (725516390)
% 0.21/0.49  ipcrm: permission denied for id (725549159)
% 0.21/0.49  ipcrm: permission denied for id (725581928)
% 0.21/0.50  ipcrm: permission denied for id (728105066)
% 0.21/0.50  ipcrm: permission denied for id (722272363)
% 0.21/0.50  ipcrm: permission denied for id (729153644)
% 0.21/0.50  ipcrm: permission denied for id (728203374)
% 0.21/0.50  ipcrm: permission denied for id (722337903)
% 0.21/0.50  ipcrm: permission denied for id (725811312)
% 0.21/0.50  ipcrm: permission denied for id (722370673)
% 0.21/0.51  ipcrm: permission denied for id (728268914)
% 0.21/0.51  ipcrm: permission denied for id (725876851)
% 0.21/0.51  ipcrm: permission denied for id (725909620)
% 0.21/0.51  ipcrm: permission denied for id (725942389)
% 0.21/0.51  ipcrm: permission denied for id (726007926)
% 0.21/0.51  ipcrm: permission denied for id (722436215)
% 0.21/0.51  ipcrm: permission denied for id (726073464)
% 0.21/0.51  ipcrm: permission denied for id (726106233)
% 0.21/0.52  ipcrm: permission denied for id (728301690)
% 0.21/0.52  ipcrm: permission denied for id (728367228)
% 0.21/0.52  ipcrm: permission denied for id (728399997)
% 0.21/0.52  ipcrm: permission denied for id (726270078)
% 0.21/0.52  ipcrm: permission denied for id (728432767)
% 0.49/0.62  % (1962)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.49/0.62  % (1950)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.49/0.62  % (1957)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.49/0.62  % (1957)Refutation not found, incomplete strategy% (1957)------------------------------
% 0.49/0.62  % (1957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.49/0.62  % (1957)Termination reason: Refutation not found, incomplete strategy
% 0.49/0.62  
% 0.49/0.62  % (1957)Memory used [KB]: 10618
% 0.49/0.62  % (1957)Time elapsed: 0.067 s
% 0.49/0.62  % (1957)------------------------------
% 0.49/0.62  % (1957)------------------------------
% 0.49/0.63  % (1955)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.05/0.63  % (1959)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.05/0.64  % (1956)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.05/0.64  % (1962)Refutation found. Thanks to Tanya!
% 1.05/0.64  % SZS status Theorem for theBenchmark
% 1.05/0.64  % SZS output start Proof for theBenchmark
% 1.05/0.64  fof(f872,plain,(
% 1.05/0.64    $false),
% 1.05/0.64    inference(trivial_inequality_removal,[],[f855])).
% 1.05/0.64  fof(f855,plain,(
% 1.05/0.64    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.05/0.64    inference(superposition,[],[f108,f20])).
% 1.05/0.64  fof(f20,plain,(
% 1.05/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.05/0.64    inference(cnf_transformation,[],[f4])).
% 1.05/0.64  fof(f4,axiom,(
% 1.05/0.64    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.05/0.64  fof(f108,plain,(
% 1.05/0.64    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 1.05/0.64    inference(forward_demodulation,[],[f94,f47])).
% 1.05/0.64  fof(f47,plain,(
% 1.05/0.64    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 1.05/0.64    inference(forward_demodulation,[],[f39,f14])).
% 1.05/0.64  fof(f14,plain,(
% 1.05/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.05/0.64    inference(cnf_transformation,[],[f3])).
% 1.05/0.64  fof(f3,axiom,(
% 1.05/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.05/0.64  fof(f39,plain,(
% 1.05/0.64    ( ! [X6,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0)) )),
% 1.05/0.64    inference(superposition,[],[f16,f22])).
% 1.05/0.64  fof(f22,plain,(
% 1.05/0.64    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.05/0.64    inference(resolution,[],[f18,f15])).
% 1.05/0.64  fof(f15,plain,(
% 1.05/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f1])).
% 1.05/0.64  fof(f1,axiom,(
% 1.05/0.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.05/0.64  fof(f18,plain,(
% 1.05/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.05/0.64    inference(cnf_transformation,[],[f12])).
% 1.05/0.64  fof(f12,plain,(
% 1.05/0.64    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.05/0.64    inference(nnf_transformation,[],[f2])).
% 1.05/0.64  fof(f2,axiom,(
% 1.05/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.05/0.64  fof(f16,plain,(
% 1.05/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f5])).
% 1.05/0.64  fof(f5,axiom,(
% 1.05/0.64    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.05/0.64  fof(f94,plain,(
% 1.05/0.64    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2)),
% 1.05/0.64    inference(superposition,[],[f13,f19])).
% 1.05/0.64  fof(f19,plain,(
% 1.05/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f6])).
% 1.05/0.64  fof(f6,axiom,(
% 1.05/0.64    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.05/0.64  fof(f13,plain,(
% 1.05/0.64    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 1.05/0.64    inference(cnf_transformation,[],[f11])).
% 1.05/0.64  fof(f11,plain,(
% 1.05/0.64    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 1.05/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 1.05/0.64  fof(f10,plain,(
% 1.05/0.64    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 1.05/0.64    introduced(choice_axiom,[])).
% 1.05/0.64  fof(f9,plain,(
% 1.05/0.64    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.05/0.64    inference(ennf_transformation,[],[f8])).
% 1.05/0.64  fof(f8,negated_conjecture,(
% 1.05/0.64    ~! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.05/0.64    inference(negated_conjecture,[],[f7])).
% 1.05/0.64  fof(f7,conjecture,(
% 1.05/0.64    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 1.05/0.64  % SZS output end Proof for theBenchmark
% 1.05/0.64  % (1962)------------------------------
% 1.05/0.64  % (1962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.05/0.64  % (1962)Termination reason: Refutation
% 1.05/0.64  
% 1.05/0.64  % (1962)Memory used [KB]: 6524
% 1.05/0.64  % (1962)Time elapsed: 0.070 s
% 1.05/0.64  % (1962)------------------------------
% 1.05/0.64  % (1962)------------------------------
% 1.05/0.64  % (1805)Success in time 0.278 s
%------------------------------------------------------------------------------
