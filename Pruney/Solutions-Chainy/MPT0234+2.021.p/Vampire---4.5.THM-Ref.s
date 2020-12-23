%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:27 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 140 expanded)
%              Number of leaves         :   11 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 ( 149 expanded)
%              Number of equality atoms :   43 ( 148 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f35,f44])).

fof(f44,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f34,f40])).

fof(f40,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f15,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f19,f32,f32,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f23,f33])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f18,f17,f32])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f35,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f16,f31,f32,f32])).

fof(f16,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:08:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (805371906)
% 0.14/0.37  ipcrm: permission denied for id (806092803)
% 0.14/0.37  ipcrm: permission denied for id (806158341)
% 0.14/0.38  ipcrm: permission denied for id (806191110)
% 0.14/0.38  ipcrm: permission denied for id (806256648)
% 0.14/0.38  ipcrm: permission denied for id (806354955)
% 0.14/0.38  ipcrm: permission denied for id (806420493)
% 0.14/0.39  ipcrm: permission denied for id (806453262)
% 0.14/0.39  ipcrm: permission denied for id (806486031)
% 0.14/0.39  ipcrm: permission denied for id (806518800)
% 0.14/0.39  ipcrm: permission denied for id (806649876)
% 0.14/0.39  ipcrm: permission denied for id (806682645)
% 0.14/0.40  ipcrm: permission denied for id (806715414)
% 0.14/0.40  ipcrm: permission denied for id (806748183)
% 0.14/0.40  ipcrm: permission denied for id (806780952)
% 0.14/0.40  ipcrm: permission denied for id (806813721)
% 0.14/0.40  ipcrm: permission denied for id (806879259)
% 0.14/0.40  ipcrm: permission denied for id (806912028)
% 0.14/0.40  ipcrm: permission denied for id (806944797)
% 0.21/0.41  ipcrm: permission denied for id (807043104)
% 0.21/0.41  ipcrm: permission denied for id (807075873)
% 0.21/0.41  ipcrm: permission denied for id (805503010)
% 0.21/0.41  ipcrm: permission denied for id (807108643)
% 0.21/0.41  ipcrm: permission denied for id (807141412)
% 0.21/0.42  ipcrm: permission denied for id (807370794)
% 0.21/0.43  ipcrm: permission denied for id (807534639)
% 0.21/0.43  ipcrm: permission denied for id (805535792)
% 0.21/0.43  ipcrm: permission denied for id (807665716)
% 0.21/0.43  ipcrm: permission denied for id (807698485)
% 0.21/0.43  ipcrm: permission denied for id (807731254)
% 0.21/0.44  ipcrm: permission denied for id (807764023)
% 0.21/0.44  ipcrm: permission denied for id (807862330)
% 0.21/0.44  ipcrm: permission denied for id (805634109)
% 0.21/0.45  ipcrm: permission denied for id (807993407)
% 0.21/0.45  ipcrm: permission denied for id (808026176)
% 0.21/0.45  ipcrm: permission denied for id (808091714)
% 0.21/0.45  ipcrm: permission denied for id (808124483)
% 0.21/0.45  ipcrm: permission denied for id (808157252)
% 0.21/0.46  ipcrm: permission denied for id (808288327)
% 0.21/0.46  ipcrm: permission denied for id (805732424)
% 0.21/0.46  ipcrm: permission denied for id (808321097)
% 0.21/0.46  ipcrm: permission denied for id (808353866)
% 0.21/0.46  ipcrm: permission denied for id (808386635)
% 0.21/0.46  ipcrm: permission denied for id (808419404)
% 0.21/0.46  ipcrm: permission denied for id (808452173)
% 0.21/0.46  ipcrm: permission denied for id (808484942)
% 0.21/0.47  ipcrm: permission denied for id (808517711)
% 0.21/0.47  ipcrm: permission denied for id (808583248)
% 0.21/0.47  ipcrm: permission denied for id (805797972)
% 0.21/0.47  ipcrm: permission denied for id (808747094)
% 0.21/0.48  ipcrm: permission denied for id (808812632)
% 0.21/0.48  ipcrm: permission denied for id (808878170)
% 0.21/0.48  ipcrm: permission denied for id (805863518)
% 0.21/0.49  ipcrm: permission denied for id (809009247)
% 0.21/0.49  ipcrm: permission denied for id (809042016)
% 0.21/0.49  ipcrm: permission denied for id (809074785)
% 0.21/0.49  ipcrm: permission denied for id (809140323)
% 0.21/0.49  ipcrm: permission denied for id (809238630)
% 0.21/0.50  ipcrm: permission denied for id (809304168)
% 0.21/0.50  ipcrm: permission denied for id (809336937)
% 0.21/0.50  ipcrm: permission denied for id (809369706)
% 0.21/0.50  ipcrm: permission denied for id (809435244)
% 0.21/0.50  ipcrm: permission denied for id (809468013)
% 0.21/0.51  ipcrm: permission denied for id (809566320)
% 0.21/0.51  ipcrm: permission denied for id (809599089)
% 0.21/0.51  ipcrm: permission denied for id (809664627)
% 0.21/0.51  ipcrm: permission denied for id (809697396)
% 0.21/0.52  ipcrm: permission denied for id (809926778)
% 0.21/0.52  ipcrm: permission denied for id (809959547)
% 0.21/0.52  ipcrm: permission denied for id (809992316)
% 0.21/0.52  ipcrm: permission denied for id (810025085)
% 0.21/0.52  ipcrm: permission denied for id (810090623)
% 0.82/0.63  % (20697)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.09/0.65  % (20690)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.09/0.65  % (20697)Refutation not found, incomplete strategy% (20697)------------------------------
% 1.09/0.65  % (20697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.09/0.65  % (20697)Termination reason: Refutation not found, incomplete strategy
% 1.09/0.65  
% 1.09/0.65  % (20697)Memory used [KB]: 10618
% 1.09/0.65  % (20697)Time elapsed: 0.087 s
% 1.09/0.65  % (20697)------------------------------
% 1.09/0.65  % (20697)------------------------------
% 1.09/0.65  % (20690)Refutation found. Thanks to Tanya!
% 1.09/0.65  % SZS status Theorem for theBenchmark
% 1.09/0.66  % (20705)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.09/0.66  % SZS output start Proof for theBenchmark
% 1.09/0.66  fof(f49,plain,(
% 1.09/0.66    $false),
% 1.09/0.66    inference(trivial_inequality_removal,[],[f48])).
% 1.09/0.66  fof(f48,plain,(
% 1.09/0.66    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 1.09/0.66    inference(superposition,[],[f35,f44])).
% 1.09/0.66  fof(f44,plain,(
% 1.09/0.66    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.09/0.66    inference(superposition,[],[f34,f40])).
% 1.09/0.66  fof(f40,plain,(
% 1.09/0.66    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.09/0.66    inference(unit_resulting_resolution,[],[f15,f37])).
% 1.09/0.66  fof(f37,plain,(
% 1.09/0.66    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 1.09/0.66    inference(definition_unfolding,[],[f19,f32,f32,f32])).
% 1.09/0.66  fof(f32,plain,(
% 1.09/0.66    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.09/0.66    inference(definition_unfolding,[],[f21,f31])).
% 1.09/0.66  fof(f31,plain,(
% 1.09/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.09/0.66    inference(definition_unfolding,[],[f22,f30])).
% 1.09/0.66  fof(f30,plain,(
% 1.09/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.09/0.66    inference(definition_unfolding,[],[f25,f29])).
% 1.09/0.66  fof(f29,plain,(
% 1.09/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.09/0.66    inference(definition_unfolding,[],[f27,f28])).
% 1.09/0.66  fof(f28,plain,(
% 1.09/0.66    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.09/0.66    inference(definition_unfolding,[],[f26,f24])).
% 1.09/0.66  fof(f24,plain,(
% 1.09/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.09/0.66    inference(cnf_transformation,[],[f9])).
% 1.09/0.66  fof(f9,axiom,(
% 1.09/0.66    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.09/0.66  fof(f26,plain,(
% 1.09/0.66    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.09/0.66    inference(cnf_transformation,[],[f8])).
% 1.09/0.66  fof(f8,axiom,(
% 1.09/0.66    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.09/0.66  fof(f27,plain,(
% 1.09/0.66    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.09/0.66    inference(cnf_transformation,[],[f7])).
% 1.09/0.66  fof(f7,axiom,(
% 1.09/0.66    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.09/0.66  fof(f25,plain,(
% 1.09/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.09/0.66    inference(cnf_transformation,[],[f6])).
% 1.09/0.66  fof(f6,axiom,(
% 1.09/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.09/0.66  fof(f22,plain,(
% 1.09/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.09/0.66    inference(cnf_transformation,[],[f5])).
% 1.09/0.66  fof(f5,axiom,(
% 1.09/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.09/0.66  fof(f21,plain,(
% 1.09/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.09/0.66    inference(cnf_transformation,[],[f4])).
% 1.09/0.66  fof(f4,axiom,(
% 1.09/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.09/0.66  fof(f19,plain,(
% 1.09/0.66    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.09/0.66    inference(cnf_transformation,[],[f11])).
% 1.09/0.66  fof(f11,axiom,(
% 1.09/0.66    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.09/0.66  fof(f15,plain,(
% 1.09/0.66    sK0 != sK1),
% 1.09/0.66    inference(cnf_transformation,[],[f14])).
% 1.09/0.66  fof(f14,plain,(
% 1.09/0.66    ? [X0,X1] : (k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1)),
% 1.09/0.66    inference(ennf_transformation,[],[f13])).
% 1.09/0.66  fof(f13,negated_conjecture,(
% 1.09/0.66    ~! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.09/0.66    inference(negated_conjecture,[],[f12])).
% 1.09/0.66  fof(f12,conjecture,(
% 1.09/0.66    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 1.09/0.66  fof(f34,plain,(
% 1.09/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) )),
% 1.09/0.66    inference(definition_unfolding,[],[f23,f33])).
% 1.09/0.66  fof(f33,plain,(
% 1.09/0.66    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))) )),
% 1.09/0.66    inference(definition_unfolding,[],[f18,f17,f32])).
% 1.09/0.66  fof(f17,plain,(
% 1.09/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.09/0.66    inference(cnf_transformation,[],[f2])).
% 1.09/0.66  fof(f2,axiom,(
% 1.09/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.09/0.66  fof(f18,plain,(
% 1.09/0.66    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 1.09/0.66    inference(cnf_transformation,[],[f3])).
% 1.09/0.66  fof(f3,axiom,(
% 1.09/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 1.09/0.66  fof(f23,plain,(
% 1.09/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.09/0.66    inference(cnf_transformation,[],[f10])).
% 1.09/0.66  fof(f10,axiom,(
% 1.09/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.09/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.09/0.66  fof(f35,plain,(
% 1.09/0.66    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.09/0.66    inference(definition_unfolding,[],[f16,f31,f32,f32])).
% 1.09/0.66  fof(f16,plain,(
% 1.09/0.66    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.09/0.66    inference(cnf_transformation,[],[f14])).
% 1.09/0.66  % SZS output end Proof for theBenchmark
% 1.09/0.66  % (20690)------------------------------
% 1.09/0.66  % (20690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.09/0.66  % (20690)Termination reason: Refutation
% 1.09/0.66  
% 1.09/0.66  % (20690)Memory used [KB]: 6268
% 1.09/0.66  % (20690)Time elapsed: 0.089 s
% 1.09/0.66  % (20690)------------------------------
% 1.09/0.66  % (20690)------------------------------
% 1.09/0.66  % (20547)Success in time 0.298 s
%------------------------------------------------------------------------------
