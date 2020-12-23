%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  25 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f52])).

fof(f52,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f10,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X3,X0,X1),k1_tarski(X2)) = k2_enumset1(X3,X0,X1,X2) ),
    inference(forward_demodulation,[],[f32,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X3,X0,X1),k1_tarski(X2)) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f29,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f29,plain,(
    ! [X6,X8,X7,X9] : k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X6,X7),X9)) = k2_xboole_0(k1_enumset1(X8,X6,X7),X9) ),
    inference(forward_demodulation,[],[f23,f12])).

fof(f23,plain,(
    ! [X6,X8,X7,X9] : k2_xboole_0(k2_xboole_0(k2_tarski(X8,X6),k1_tarski(X7)),X9) = k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X6,X7),X9)) ),
    inference(superposition,[],[f15,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),X2),X3)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),X2),X3) ),
    inference(superposition,[],[f14,f11])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:33:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.38  ipcrm: permission denied for id (785874945)
% 0.14/0.38  ipcrm: permission denied for id (790265858)
% 0.14/0.39  ipcrm: permission denied for id (791773187)
% 0.14/0.39  ipcrm: permission denied for id (790331396)
% 0.14/0.39  ipcrm: permission denied for id (791805957)
% 0.14/0.39  ipcrm: permission denied for id (786333702)
% 0.14/0.39  ipcrm: permission denied for id (785907719)
% 0.14/0.39  ipcrm: permission denied for id (786366472)
% 0.14/0.39  ipcrm: permission denied for id (786399241)
% 0.14/0.39  ipcrm: permission denied for id (786432010)
% 0.14/0.40  ipcrm: permission denied for id (790396939)
% 0.14/0.40  ipcrm: permission denied for id (786497548)
% 0.14/0.40  ipcrm: permission denied for id (786530317)
% 0.14/0.40  ipcrm: permission denied for id (792821774)
% 0.14/0.40  ipcrm: permission denied for id (786595855)
% 0.14/0.40  ipcrm: permission denied for id (786628624)
% 0.14/0.40  ipcrm: permission denied for id (786661393)
% 0.14/0.40  ipcrm: permission denied for id (786694162)
% 0.14/0.40  ipcrm: permission denied for id (786726931)
% 0.14/0.41  ipcrm: permission denied for id (791871508)
% 0.14/0.41  ipcrm: permission denied for id (786792469)
% 0.14/0.41  ipcrm: permission denied for id (786858007)
% 0.14/0.41  ipcrm: permission denied for id (785940504)
% 0.14/0.41  ipcrm: permission denied for id (786890777)
% 0.14/0.41  ipcrm: permission denied for id (790560794)
% 0.14/0.41  ipcrm: permission denied for id (790593563)
% 0.14/0.41  ipcrm: permission denied for id (786989084)
% 0.14/0.41  ipcrm: permission denied for id (787021853)
% 0.14/0.41  ipcrm: permission denied for id (787054622)
% 0.14/0.42  ipcrm: permission denied for id (787087391)
% 0.14/0.42  ipcrm: permission denied for id (787120160)
% 0.14/0.42  ipcrm: permission denied for id (787152929)
% 0.14/0.42  ipcrm: permission denied for id (791937058)
% 0.14/0.42  ipcrm: permission denied for id (787218467)
% 0.14/0.42  ipcrm: permission denied for id (790659108)
% 0.22/0.42  ipcrm: permission denied for id (787284005)
% 0.22/0.42  ipcrm: permission denied for id (791969830)
% 0.22/0.42  ipcrm: permission denied for id (787349543)
% 0.22/0.42  ipcrm: permission denied for id (787382312)
% 0.22/0.42  ipcrm: permission denied for id (790724649)
% 0.22/0.43  ipcrm: permission denied for id (787447850)
% 0.22/0.43  ipcrm: permission denied for id (787480619)
% 0.22/0.43  ipcrm: permission denied for id (790757420)
% 0.22/0.43  ipcrm: permission denied for id (787546157)
% 0.22/0.43  ipcrm: permission denied for id (787578926)
% 0.22/0.43  ipcrm: permission denied for id (787611695)
% 0.22/0.43  ipcrm: permission denied for id (792002608)
% 0.22/0.43  ipcrm: permission denied for id (787677233)
% 0.22/0.43  ipcrm: permission denied for id (792035378)
% 0.22/0.43  ipcrm: permission denied for id (787742771)
% 0.22/0.43  ipcrm: permission denied for id (790855732)
% 0.22/0.44  ipcrm: permission denied for id (787808309)
% 0.22/0.44  ipcrm: permission denied for id (790888502)
% 0.22/0.44  ipcrm: permission denied for id (787873847)
% 0.22/0.44  ipcrm: permission denied for id (792068152)
% 0.22/0.44  ipcrm: permission denied for id (787939385)
% 0.22/0.44  ipcrm: permission denied for id (792100922)
% 0.22/0.44  ipcrm: permission denied for id (788004923)
% 0.22/0.44  ipcrm: permission denied for id (792133692)
% 0.22/0.44  ipcrm: permission denied for id (788070461)
% 0.22/0.44  ipcrm: permission denied for id (792166462)
% 0.22/0.45  ipcrm: permission denied for id (788135999)
% 0.22/0.45  ipcrm: permission denied for id (788168768)
% 0.22/0.45  ipcrm: permission denied for id (788201537)
% 0.22/0.45  ipcrm: permission denied for id (788234306)
% 0.22/0.45  ipcrm: permission denied for id (788267075)
% 0.22/0.45  ipcrm: permission denied for id (785973316)
% 0.22/0.45  ipcrm: permission denied for id (788299845)
% 0.22/0.45  ipcrm: permission denied for id (788332614)
% 0.22/0.45  ipcrm: permission denied for id (788365383)
% 0.22/0.45  ipcrm: permission denied for id (792887368)
% 0.22/0.45  ipcrm: permission denied for id (788430921)
% 0.22/0.46  ipcrm: permission denied for id (788463690)
% 0.22/0.46  ipcrm: permission denied for id (788496459)
% 0.22/0.46  ipcrm: permission denied for id (788529228)
% 0.22/0.46  ipcrm: permission denied for id (788561997)
% 0.22/0.46  ipcrm: permission denied for id (792952911)
% 0.22/0.46  ipcrm: permission denied for id (793575504)
% 0.22/0.46  ipcrm: permission denied for id (788725842)
% 0.22/0.46  ipcrm: permission denied for id (788758611)
% 0.22/0.46  ipcrm: permission denied for id (788791380)
% 0.22/0.47  ipcrm: permission denied for id (793051221)
% 0.22/0.47  ipcrm: permission denied for id (788856918)
% 0.22/0.47  ipcrm: permission denied for id (788922456)
% 0.22/0.47  ipcrm: permission denied for id (788955225)
% 0.22/0.47  ipcrm: permission denied for id (788987994)
% 0.22/0.47  ipcrm: permission denied for id (789020763)
% 0.22/0.47  ipcrm: permission denied for id (789053532)
% 0.22/0.47  ipcrm: permission denied for id (789086301)
% 0.22/0.47  ipcrm: permission denied for id (793116766)
% 0.22/0.47  ipcrm: permission denied for id (789151839)
% 0.22/0.47  ipcrm: permission denied for id (792461408)
% 0.22/0.48  ipcrm: permission denied for id (789217377)
% 0.22/0.48  ipcrm: permission denied for id (789282915)
% 0.22/0.48  ipcrm: permission denied for id (793182308)
% 0.22/0.48  ipcrm: permission denied for id (789348453)
% 0.22/0.48  ipcrm: permission denied for id (793706598)
% 0.22/0.48  ipcrm: permission denied for id (789413991)
% 0.22/0.48  ipcrm: permission denied for id (789446760)
% 0.22/0.48  ipcrm: permission denied for id (793247849)
% 0.22/0.48  ipcrm: permission denied for id (793280618)
% 0.22/0.48  ipcrm: permission denied for id (789545067)
% 0.22/0.48  ipcrm: permission denied for id (793313388)
% 0.22/0.48  ipcrm: permission denied for id (789610605)
% 0.22/0.49  ipcrm: permission denied for id (789643374)
% 0.22/0.49  ipcrm: permission denied for id (789676143)
% 0.22/0.49  ipcrm: permission denied for id (789708912)
% 0.22/0.49  ipcrm: permission denied for id (789741681)
% 0.22/0.49  ipcrm: permission denied for id (789774450)
% 0.22/0.49  ipcrm: permission denied for id (789839988)
% 0.22/0.49  ipcrm: permission denied for id (791576693)
% 0.22/0.49  ipcrm: permission denied for id (789905526)
% 0.22/0.49  ipcrm: permission denied for id (789971064)
% 0.22/0.49  ipcrm: permission denied for id (791642233)
% 0.22/0.49  ipcrm: permission denied for id (790036602)
% 0.22/0.49  ipcrm: permission denied for id (793804923)
% 0.22/0.50  ipcrm: permission denied for id (790102140)
% 0.22/0.50  ipcrm: permission denied for id (790134909)
% 0.22/0.50  ipcrm: permission denied for id (791707774)
% 0.22/0.50  ipcrm: permission denied for id (790200447)
% 0.22/0.56  % (28353)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.56  % (28362)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.56  % (28353)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (28356)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)),
% 0.22/0.56    inference(superposition,[],[f10,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X3,X0,X1),k1_tarski(X2)) = k2_enumset1(X3,X0,X1,X2)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f32,f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X3,X0,X1),k1_tarski(X2)) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 0.22/0.56    inference(superposition,[],[f29,f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X6,X8,X7,X9] : (k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X6,X7),X9)) = k2_xboole_0(k1_enumset1(X8,X6,X7),X9)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f23,f12])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ( ! [X6,X8,X7,X9] : (k2_xboole_0(k2_xboole_0(k2_tarski(X8,X6),k1_tarski(X7)),X9) = k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X6,X7),X9))) )),
% 0.22/0.56    inference(superposition,[],[f15,f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),X2),X3)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),X2),X3)) )),
% 0.22/0.56    inference(superposition,[],[f14,f11])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.22/0.56  fof(f8,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f7,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.56    inference(negated_conjecture,[],[f5])).
% 0.22/0.56  fof(f5,conjecture,(
% 0.22/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (28353)------------------------------
% 0.22/0.56  % (28353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28353)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (28353)Memory used [KB]: 1663
% 0.22/0.56  % (28353)Time elapsed: 0.028 s
% 0.22/0.56  % (28353)------------------------------
% 0.22/0.56  % (28353)------------------------------
% 0.22/0.56  % (28354)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.57  % (28212)Success in time 0.195 s
%------------------------------------------------------------------------------
