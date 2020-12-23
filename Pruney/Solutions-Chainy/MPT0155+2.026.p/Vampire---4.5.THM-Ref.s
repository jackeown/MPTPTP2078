%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:39 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   31 (  46 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   32 (  47 expanded)
%              Number of equality atoms :   31 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[],[f17,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(forward_demodulation,[],[f93,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_enumset1(X1,X2,X0,X0,X0) = k1_enumset1(X1,X2,X0) ),
    inference(forward_demodulation,[],[f49,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_enumset1(X1,X2,X0,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f33,f18])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f23,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f93,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2) ),
    inference(superposition,[],[f70,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(forward_demodulation,[],[f41,f23])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(superposition,[],[f25,f19])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f70,plain,(
    ! [X12,X10,X11,X9] : k4_enumset1(X12,X9,X10,X11,X11,X11) = k2_enumset1(X12,X9,X10,X11) ),
    inference(forward_demodulation,[],[f64,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f64,plain,(
    ! [X12,X10,X11,X9] : k4_enumset1(X12,X9,X10,X11,X11,X11) = k2_xboole_0(k1_tarski(X12),k1_enumset1(X9,X10,X11)) ),
    inference(superposition,[],[f24,f54])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f17,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:32:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (812843008)
% 0.14/0.37  ipcrm: permission denied for id (821067778)
% 0.14/0.37  ipcrm: permission denied for id (815529987)
% 0.14/0.37  ipcrm: permission denied for id (815562756)
% 0.14/0.37  ipcrm: permission denied for id (815595525)
% 0.14/0.37  ipcrm: permission denied for id (815628294)
% 0.14/0.37  ipcrm: permission denied for id (815661063)
% 0.14/0.38  ipcrm: permission denied for id (815693832)
% 0.14/0.38  ipcrm: permission denied for id (818610185)
% 0.14/0.38  ipcrm: permission denied for id (813006858)
% 0.14/0.38  ipcrm: permission denied for id (813039627)
% 0.14/0.38  ipcrm: permission denied for id (815759372)
% 0.14/0.38  ipcrm: permission denied for id (818642957)
% 0.14/0.38  ipcrm: permission denied for id (819986446)
% 0.14/0.38  ipcrm: permission denied for id (815857679)
% 0.14/0.39  ipcrm: permission denied for id (813170704)
% 0.14/0.39  ipcrm: permission denied for id (818708497)
% 0.14/0.39  ipcrm: permission denied for id (813236242)
% 0.14/0.39  ipcrm: permission denied for id (815923219)
% 0.14/0.39  ipcrm: permission denied for id (815955988)
% 0.14/0.39  ipcrm: permission denied for id (818741269)
% 0.14/0.39  ipcrm: permission denied for id (816021526)
% 0.14/0.39  ipcrm: permission denied for id (816054295)
% 0.14/0.40  ipcrm: permission denied for id (816087064)
% 0.14/0.40  ipcrm: permission denied for id (818774041)
% 0.14/0.40  ipcrm: permission denied for id (816152602)
% 0.20/0.40  ipcrm: permission denied for id (816185371)
% 0.20/0.40  ipcrm: permission denied for id (820019228)
% 0.20/0.40  ipcrm: permission denied for id (820051997)
% 0.20/0.40  ipcrm: permission denied for id (816283678)
% 0.20/0.40  ipcrm: permission denied for id (820084767)
% 0.20/0.41  ipcrm: permission denied for id (813432864)
% 0.20/0.41  ipcrm: permission denied for id (813465633)
% 0.20/0.41  ipcrm: permission denied for id (816349218)
% 0.20/0.41  ipcrm: permission denied for id (818905123)
% 0.20/0.41  ipcrm: permission denied for id (816414756)
% 0.20/0.41  ipcrm: permission denied for id (816447525)
% 0.20/0.41  ipcrm: permission denied for id (818937894)
% 0.20/0.41  ipcrm: permission denied for id (816513063)
% 0.20/0.42  ipcrm: permission denied for id (818970664)
% 0.20/0.42  ipcrm: permission denied for id (813596713)
% 0.20/0.42  ipcrm: permission denied for id (813629482)
% 0.20/0.42  ipcrm: permission denied for id (816578603)
% 0.20/0.42  ipcrm: permission denied for id (816611372)
% 0.20/0.42  ipcrm: permission denied for id (813727789)
% 0.20/0.42  ipcrm: permission denied for id (819003438)
% 0.20/0.42  ipcrm: permission denied for id (820117551)
% 0.20/0.43  ipcrm: permission denied for id (816709680)
% 0.20/0.43  ipcrm: permission denied for id (816742449)
% 0.20/0.43  ipcrm: permission denied for id (819068978)
% 0.20/0.43  ipcrm: permission denied for id (820740147)
% 0.20/0.43  ipcrm: permission denied for id (813793332)
% 0.20/0.43  ipcrm: permission denied for id (820183093)
% 0.20/0.43  ipcrm: permission denied for id (816873526)
% 0.20/0.44  ipcrm: permission denied for id (821100599)
% 0.20/0.44  ipcrm: permission denied for id (816939064)
% 0.20/0.44  ipcrm: permission denied for id (816971833)
% 0.20/0.44  ipcrm: permission denied for id (817004602)
% 0.20/0.44  ipcrm: permission denied for id (813891643)
% 0.20/0.44  ipcrm: permission denied for id (817037372)
% 0.20/0.45  ipcrm: permission denied for id (819200061)
% 0.20/0.45  ipcrm: permission denied for id (820805694)
% 0.20/0.45  ipcrm: permission denied for id (819265599)
% 0.20/0.45  ipcrm: permission denied for id (817168448)
% 0.20/0.45  ipcrm: permission denied for id (814055489)
% 0.20/0.45  ipcrm: permission denied for id (814088258)
% 0.20/0.45  ipcrm: permission denied for id (817201219)
% 0.20/0.46  ipcrm: permission denied for id (819298372)
% 0.20/0.46  ipcrm: permission denied for id (817266757)
% 0.20/0.46  ipcrm: permission denied for id (817299526)
% 0.20/0.46  ipcrm: permission denied for id (814153799)
% 0.20/0.46  ipcrm: permission denied for id (814186568)
% 0.20/0.46  ipcrm: permission denied for id (817332297)
% 0.20/0.47  ipcrm: permission denied for id (819331146)
% 0.20/0.47  ipcrm: permission denied for id (817397835)
% 0.20/0.47  ipcrm: permission denied for id (814252108)
% 0.20/0.47  ipcrm: permission denied for id (820281421)
% 0.20/0.47  ipcrm: permission denied for id (817463374)
% 0.20/0.47  ipcrm: permission denied for id (817496143)
% 0.20/0.47  ipcrm: permission denied for id (814317648)
% 0.20/0.48  ipcrm: permission denied for id (817528913)
% 0.20/0.48  ipcrm: permission denied for id (814350418)
% 0.20/0.48  ipcrm: permission denied for id (820314195)
% 0.20/0.48  ipcrm: permission denied for id (817594452)
% 0.20/0.48  ipcrm: permission denied for id (814448725)
% 0.20/0.48  ipcrm: permission denied for id (814481494)
% 0.20/0.48  ipcrm: permission denied for id (817627223)
% 0.20/0.49  ipcrm: permission denied for id (819429464)
% 0.20/0.49  ipcrm: permission denied for id (814547033)
% 0.20/0.49  ipcrm: permission denied for id (817692762)
% 0.20/0.49  ipcrm: permission denied for id (814579803)
% 0.20/0.49  ipcrm: permission denied for id (820346972)
% 0.20/0.49  ipcrm: permission denied for id (814645341)
% 0.20/0.50  ipcrm: permission denied for id (814678110)
% 0.20/0.50  ipcrm: permission denied for id (814710879)
% 0.20/0.50  ipcrm: permission denied for id (820379744)
% 0.20/0.50  ipcrm: permission denied for id (814743649)
% 0.20/0.50  ipcrm: permission denied for id (817791074)
% 0.20/0.50  ipcrm: permission denied for id (819527779)
% 0.20/0.50  ipcrm: permission denied for id (821133412)
% 0.20/0.51  ipcrm: permission denied for id (814841957)
% 0.20/0.51  ipcrm: permission denied for id (814874726)
% 0.20/0.51  ipcrm: permission denied for id (819593319)
% 0.20/0.51  ipcrm: permission denied for id (817922152)
% 0.20/0.51  ipcrm: permission denied for id (814907497)
% 0.20/0.51  ipcrm: permission denied for id (821166186)
% 0.20/0.52  ipcrm: permission denied for id (814940268)
% 0.20/0.52  ipcrm: permission denied for id (818020461)
% 0.20/0.52  ipcrm: permission denied for id (818085998)
% 0.20/0.52  ipcrm: permission denied for id (815038575)
% 0.20/0.52  ipcrm: permission denied for id (818118768)
% 0.20/0.52  ipcrm: permission denied for id (821231729)
% 0.20/0.52  ipcrm: permission denied for id (818184306)
% 0.20/0.53  ipcrm: permission denied for id (819724403)
% 0.20/0.53  ipcrm: permission denied for id (818249844)
% 0.20/0.53  ipcrm: permission denied for id (820576373)
% 0.20/0.53  ipcrm: permission denied for id (815235190)
% 0.20/0.53  ipcrm: permission denied for id (815267959)
% 0.20/0.53  ipcrm: permission denied for id (820969592)
% 0.20/0.54  ipcrm: permission denied for id (819822713)
% 0.20/0.54  ipcrm: permission denied for id (815333498)
% 0.20/0.54  ipcrm: permission denied for id (818413691)
% 0.20/0.54  ipcrm: permission denied for id (815366268)
% 0.20/0.54  ipcrm: permission denied for id (818446461)
% 0.20/0.54  ipcrm: permission denied for id (821002366)
% 0.20/0.54  ipcrm: permission denied for id (819888255)
% 0.20/0.60  % (783)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.60  % (783)Refutation not found, incomplete strategy% (783)------------------------------
% 0.20/0.60  % (783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (783)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (783)Memory used [KB]: 10490
% 0.20/0.60  % (783)Time elapsed: 0.003 s
% 0.20/0.60  % (783)------------------------------
% 0.20/0.60  % (783)------------------------------
% 0.83/0.62  % (775)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.83/0.63  % (776)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.88/0.63  % (775)Refutation found. Thanks to Tanya!
% 0.88/0.63  % SZS status Theorem for theBenchmark
% 0.88/0.63  % SZS output start Proof for theBenchmark
% 0.88/0.63  fof(f114,plain,(
% 0.88/0.63    $false),
% 0.88/0.63    inference(trivial_inequality_removal,[],[f111])).
% 0.88/0.63  fof(f111,plain,(
% 0.88/0.63    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)),
% 0.88/0.63    inference(superposition,[],[f17,f95])).
% 0.88/0.63  fof(f95,plain,(
% 0.88/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.88/0.63    inference(forward_demodulation,[],[f93,f54])).
% 0.88/0.63  fof(f54,plain,(
% 0.88/0.63    ( ! [X2,X0,X1] : (k3_enumset1(X1,X2,X0,X0,X0) = k1_enumset1(X1,X2,X0)) )),
% 0.88/0.63    inference(forward_demodulation,[],[f49,f21])).
% 0.88/0.63  fof(f21,plain,(
% 0.88/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.88/0.63    inference(cnf_transformation,[],[f3])).
% 0.88/0.63  fof(f3,axiom,(
% 0.88/0.63    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.88/0.63  fof(f49,plain,(
% 0.88/0.63    ( ! [X2,X0,X1] : (k3_enumset1(X1,X2,X0,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 0.88/0.63    inference(superposition,[],[f33,f18])).
% 0.88/0.63  fof(f18,plain,(
% 0.88/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f10])).
% 0.88/0.63  fof(f10,axiom,(
% 0.88/0.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.88/0.63  fof(f33,plain,(
% 0.88/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) )),
% 0.88/0.63    inference(superposition,[],[f23,f19])).
% 0.88/0.63  fof(f19,plain,(
% 0.88/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.88/0.63    inference(cnf_transformation,[],[f11])).
% 0.88/0.63  fof(f11,axiom,(
% 0.88/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.88/0.63  fof(f23,plain,(
% 0.88/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.88/0.63    inference(cnf_transformation,[],[f5])).
% 0.88/0.63  fof(f5,axiom,(
% 0.88/0.63    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.88/0.63  fof(f93,plain,(
% 0.88/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k3_enumset1(X0,X1,X2,X2,X2)) )),
% 0.88/0.63    inference(superposition,[],[f70,f43])).
% 0.88/0.63  fof(f43,plain,(
% 0.88/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.88/0.63    inference(forward_demodulation,[],[f41,f23])).
% 0.88/0.63  fof(f41,plain,(
% 0.88/0.63    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.88/0.63    inference(superposition,[],[f25,f19])).
% 0.88/0.63  fof(f25,plain,(
% 0.88/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.88/0.63    inference(cnf_transformation,[],[f2])).
% 0.88/0.63  fof(f2,axiom,(
% 0.88/0.63    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.88/0.63  fof(f70,plain,(
% 0.88/0.63    ( ! [X12,X10,X11,X9] : (k4_enumset1(X12,X9,X10,X11,X11,X11) = k2_enumset1(X12,X9,X10,X11)) )),
% 0.88/0.63    inference(forward_demodulation,[],[f64,f22])).
% 0.88/0.63  fof(f22,plain,(
% 0.88/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.88/0.63    inference(cnf_transformation,[],[f4])).
% 0.88/0.63  fof(f4,axiom,(
% 0.88/0.63    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.88/0.63  fof(f64,plain,(
% 0.88/0.63    ( ! [X12,X10,X11,X9] : (k4_enumset1(X12,X9,X10,X11,X11,X11) = k2_xboole_0(k1_tarski(X12),k1_enumset1(X9,X10,X11))) )),
% 0.88/0.63    inference(superposition,[],[f24,f54])).
% 0.88/0.63  fof(f24,plain,(
% 0.88/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.88/0.63    inference(cnf_transformation,[],[f6])).
% 0.88/0.63  fof(f6,axiom,(
% 0.88/0.63    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.88/0.63  fof(f17,plain,(
% 0.88/0.63    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.88/0.63    inference(cnf_transformation,[],[f16])).
% 0.88/0.63  fof(f16,plain,(
% 0.88/0.63    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.88/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 0.88/0.63  fof(f15,plain,(
% 0.88/0.63    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.88/0.63    introduced(choice_axiom,[])).
% 0.88/0.63  fof(f14,plain,(
% 0.88/0.63    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.88/0.63    inference(ennf_transformation,[],[f13])).
% 0.88/0.63  fof(f13,negated_conjecture,(
% 0.88/0.63    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.88/0.63    inference(negated_conjecture,[],[f12])).
% 0.88/0.63  fof(f12,conjecture,(
% 0.88/0.63    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.88/0.63  % SZS output end Proof for theBenchmark
% 0.88/0.63  % (775)------------------------------
% 0.88/0.63  % (775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.88/0.63  % (775)Termination reason: Refutation
% 0.88/0.63  
% 0.88/0.63  % (775)Memory used [KB]: 1663
% 0.88/0.63  % (775)Time elapsed: 0.035 s
% 0.88/0.63  % (775)------------------------------
% 0.88/0.63  % (775)------------------------------
% 0.88/0.63  % (586)Success in time 0.268 s
%------------------------------------------------------------------------------
