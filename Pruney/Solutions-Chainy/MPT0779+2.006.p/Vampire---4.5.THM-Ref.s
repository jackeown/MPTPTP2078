%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:56 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   29 (  47 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  97 expanded)
%              Number of equality atoms :   27 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f31])).

fof(f31,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0) ),
    inference(forward_demodulation,[],[f30,f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f26,f18])).

fof(f18,plain,(
    ! [X1] : k1_relat_1(sK2(X1)) = X1 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( k1_relat_1(X2) = X1
      & v1_relat_1(X2) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = o_1_0_funct_1(X0) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

fof(f26,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f25,f22])).

fof(f22,plain,(
    ! [X0] : sK2(X0) = k7_relat_1(sK2(X0),X0) ),
    inference(forward_demodulation,[],[f21,f18])).

fof(f21,plain,(
    ! [X0] : sK2(X0) = k7_relat_1(sK2(X0),k1_relat_1(sK2(X0))) ),
    inference(resolution,[],[f15,f17])).

fof(f17,plain,(
    ! [X1] : v1_relat_1(sK2(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f25,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k1_relat_1(k7_relat_1(sK2(X1),X2)) ),
    inference(forward_demodulation,[],[f24,f18])).

fof(f24,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(sK2(X1),X2)) = k3_xboole_0(k1_relat_1(sK2(X1)),X2) ),
    inference(resolution,[],[f16,f17])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f30,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,k3_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f14,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f19,f13])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(f14,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:23:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (808189952)
% 0.13/0.37  ipcrm: permission denied for id (812122114)
% 0.13/0.37  ipcrm: permission denied for id (808255491)
% 0.13/0.37  ipcrm: permission denied for id (812154884)
% 0.13/0.37  ipcrm: permission denied for id (808288261)
% 0.13/0.37  ipcrm: permission denied for id (808321030)
% 0.13/0.37  ipcrm: permission denied for id (808353799)
% 0.13/0.37  ipcrm: permission denied for id (812187656)
% 0.13/0.38  ipcrm: permission denied for id (808419337)
% 0.13/0.38  ipcrm: permission denied for id (812220426)
% 0.13/0.38  ipcrm: permission denied for id (808452107)
% 0.13/0.38  ipcrm: permission denied for id (808484876)
% 0.13/0.38  ipcrm: permission denied for id (812253197)
% 0.13/0.38  ipcrm: permission denied for id (812318735)
% 0.13/0.39  ipcrm: permission denied for id (808583185)
% 0.20/0.39  ipcrm: permission denied for id (808615954)
% 0.20/0.39  ipcrm: permission denied for id (812384275)
% 0.20/0.39  ipcrm: permission denied for id (812417044)
% 0.20/0.39  ipcrm: permission denied for id (812482582)
% 0.20/0.39  ipcrm: permission denied for id (808779799)
% 0.20/0.39  ipcrm: permission denied for id (808812568)
% 0.20/0.40  ipcrm: permission denied for id (808845337)
% 0.20/0.40  ipcrm: permission denied for id (808878106)
% 0.20/0.40  ipcrm: permission denied for id (808910875)
% 0.20/0.40  ipcrm: permission denied for id (808943644)
% 0.20/0.40  ipcrm: permission denied for id (809009181)
% 0.20/0.40  ipcrm: permission denied for id (812515358)
% 0.20/0.40  ipcrm: permission denied for id (812548127)
% 0.20/0.40  ipcrm: permission denied for id (809074720)
% 0.20/0.41  ipcrm: permission denied for id (812613666)
% 0.20/0.41  ipcrm: permission denied for id (809271334)
% 0.20/0.41  ipcrm: permission denied for id (809304103)
% 0.20/0.41  ipcrm: permission denied for id (812777512)
% 0.20/0.42  ipcrm: permission denied for id (809435178)
% 0.20/0.42  ipcrm: permission denied for id (809500716)
% 0.20/0.42  ipcrm: permission denied for id (809533485)
% 0.20/0.42  ipcrm: permission denied for id (812908591)
% 0.20/0.42  ipcrm: permission denied for id (812941360)
% 0.20/0.42  ipcrm: permission denied for id (812974129)
% 0.20/0.43  ipcrm: permission denied for id (809697330)
% 0.20/0.43  ipcrm: permission denied for id (813006899)
% 0.20/0.43  ipcrm: permission denied for id (809762868)
% 0.20/0.43  ipcrm: permission denied for id (809828406)
% 0.20/0.43  ipcrm: permission denied for id (809861175)
% 0.20/0.43  ipcrm: permission denied for id (809893944)
% 0.20/0.44  ipcrm: permission denied for id (809959482)
% 0.20/0.44  ipcrm: permission denied for id (813105211)
% 0.20/0.44  ipcrm: permission denied for id (813170749)
% 0.20/0.44  ipcrm: permission denied for id (810057790)
% 0.20/0.44  ipcrm: permission denied for id (810090559)
% 0.20/0.45  ipcrm: permission denied for id (810123328)
% 0.20/0.45  ipcrm: permission denied for id (810156097)
% 0.20/0.45  ipcrm: permission denied for id (813203522)
% 0.20/0.45  ipcrm: permission denied for id (813236291)
% 0.20/0.45  ipcrm: permission denied for id (813269060)
% 0.20/0.45  ipcrm: permission denied for id (810319942)
% 0.20/0.46  ipcrm: permission denied for id (810352711)
% 0.20/0.46  ipcrm: permission denied for id (810385480)
% 0.20/0.46  ipcrm: permission denied for id (810418249)
% 0.20/0.46  ipcrm: permission denied for id (810451018)
% 0.20/0.46  ipcrm: permission denied for id (810483787)
% 0.20/0.46  ipcrm: permission denied for id (810516556)
% 0.20/0.47  ipcrm: permission denied for id (813367374)
% 0.20/0.47  ipcrm: permission denied for id (810582095)
% 0.20/0.47  ipcrm: permission denied for id (810647633)
% 0.20/0.47  ipcrm: permission denied for id (810680402)
% 0.20/0.48  ipcrm: permission denied for id (810745940)
% 0.20/0.48  ipcrm: permission denied for id (810877016)
% 0.20/0.48  ipcrm: permission denied for id (810909785)
% 0.20/0.48  ipcrm: permission denied for id (810942554)
% 0.20/0.49  ipcrm: permission denied for id (813563995)
% 0.20/0.49  ipcrm: permission denied for id (811073631)
% 0.20/0.49  ipcrm: permission denied for id (813695072)
% 0.20/0.50  ipcrm: permission denied for id (811171938)
% 0.20/0.50  ipcrm: permission denied for id (811204707)
% 0.20/0.50  ipcrm: permission denied for id (813793381)
% 0.20/0.50  ipcrm: permission denied for id (813826150)
% 0.20/0.50  ipcrm: permission denied for id (811368552)
% 0.20/0.51  ipcrm: permission denied for id (813924458)
% 0.20/0.51  ipcrm: permission denied for id (811434091)
% 0.20/0.51  ipcrm: permission denied for id (814022766)
% 0.20/0.51  ipcrm: permission denied for id (811565167)
% 0.20/0.52  ipcrm: permission denied for id (814055536)
% 0.20/0.52  ipcrm: permission denied for id (814088305)
% 0.20/0.52  ipcrm: permission denied for id (814121074)
% 0.20/0.52  ipcrm: permission denied for id (811696243)
% 0.20/0.52  ipcrm: permission denied for id (814153844)
% 0.20/0.52  ipcrm: permission denied for id (814186613)
% 0.20/0.53  ipcrm: permission denied for id (811761782)
% 0.20/0.53  ipcrm: permission denied for id (811794551)
% 0.20/0.53  ipcrm: permission denied for id (811827320)
% 0.35/0.53  ipcrm: permission denied for id (814284923)
% 0.35/0.53  ipcrm: permission denied for id (814350461)
% 0.35/0.53  ipcrm: permission denied for id (812023934)
% 0.35/0.54  ipcrm: permission denied for id (812056703)
% 0.38/0.57  % (16585)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.38/0.58  % (16576)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.38/0.58  % (16576)Refutation found. Thanks to Tanya!
% 0.38/0.58  % SZS status Theorem for theBenchmark
% 0.38/0.58  % SZS output start Proof for theBenchmark
% 0.38/0.58  fof(f32,plain,(
% 0.38/0.58    $false),
% 0.38/0.58    inference(trivial_inequality_removal,[],[f31])).
% 0.38/0.58  fof(f31,plain,(
% 0.38/0.58    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0)),
% 0.38/0.58    inference(forward_demodulation,[],[f30,f27])).
% 0.38/0.58  fof(f27,plain,(
% 0.38/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.38/0.58    inference(forward_demodulation,[],[f26,f18])).
% 0.38/0.58  fof(f18,plain,(
% 0.38/0.58    ( ! [X1] : (k1_relat_1(sK2(X1)) = X1) )),
% 0.38/0.58    inference(cnf_transformation,[],[f8])).
% 0.38/0.58  fof(f8,plain,(
% 0.38/0.58    ! [X0,X1] : ? [X2] : (k1_relat_1(X2) = X1 & v1_relat_1(X2))),
% 0.38/0.58    inference(pure_predicate_removal,[],[f7])).
% 0.38/0.58  fof(f7,plain,(
% 0.38/0.58    ! [X0,X1] : ? [X2] : (k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.38/0.58    inference(pure_predicate_removal,[],[f3])).
% 0.38/0.58  fof(f3,axiom,(
% 0.38/0.58    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X1) => k1_funct_1(X2,X3) = o_1_0_funct_1(X0)) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).
% 0.38/0.58  fof(f26,plain,(
% 0.38/0.58    ( ! [X0] : (k1_relat_1(sK2(X0)) = k3_xboole_0(X0,X0)) )),
% 0.38/0.58    inference(superposition,[],[f25,f22])).
% 0.38/0.58  fof(f22,plain,(
% 0.38/0.58    ( ! [X0] : (sK2(X0) = k7_relat_1(sK2(X0),X0)) )),
% 0.38/0.58    inference(forward_demodulation,[],[f21,f18])).
% 0.38/0.58  fof(f21,plain,(
% 0.38/0.58    ( ! [X0] : (sK2(X0) = k7_relat_1(sK2(X0),k1_relat_1(sK2(X0)))) )),
% 0.38/0.58    inference(resolution,[],[f15,f17])).
% 0.38/0.58  fof(f17,plain,(
% 0.38/0.58    ( ! [X1] : (v1_relat_1(sK2(X1))) )),
% 0.38/0.58    inference(cnf_transformation,[],[f8])).
% 0.38/0.58  fof(f15,plain,(
% 0.38/0.58    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.38/0.58    inference(cnf_transformation,[],[f10])).
% 0.38/0.58  fof(f10,plain,(
% 0.38/0.58    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.38/0.58    inference(ennf_transformation,[],[f2])).
% 0.38/0.58  fof(f2,axiom,(
% 0.38/0.58    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.38/0.58  fof(f25,plain,(
% 0.38/0.58    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k1_relat_1(k7_relat_1(sK2(X1),X2))) )),
% 0.38/0.58    inference(forward_demodulation,[],[f24,f18])).
% 0.38/0.58  fof(f24,plain,(
% 0.38/0.58    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(sK2(X1),X2)) = k3_xboole_0(k1_relat_1(sK2(X1)),X2)) )),
% 0.38/0.58    inference(resolution,[],[f16,f17])).
% 0.38/0.58  fof(f16,plain,(
% 0.38/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.38/0.58    inference(cnf_transformation,[],[f11])).
% 0.38/0.58  fof(f11,plain,(
% 0.38/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.38/0.58    inference(ennf_transformation,[],[f1])).
% 0.38/0.58  fof(f1,axiom,(
% 0.38/0.58    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.38/0.58  fof(f30,plain,(
% 0.38/0.58    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,k3_xboole_0(sK0,sK0))),
% 0.38/0.58    inference(superposition,[],[f14,f28])).
% 0.38/0.58  fof(f28,plain,(
% 0.38/0.58    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k3_xboole_0(X0,X1))) )),
% 0.38/0.58    inference(resolution,[],[f19,f13])).
% 0.38/0.58  fof(f13,plain,(
% 0.38/0.58    v1_relat_1(sK1)),
% 0.38/0.58    inference(cnf_transformation,[],[f9])).
% 0.38/0.58  fof(f9,plain,(
% 0.38/0.58    ? [X0,X1] : (k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0) & v1_relat_1(X1))),
% 0.38/0.58    inference(ennf_transformation,[],[f6])).
% 0.38/0.58  fof(f6,negated_conjecture,(
% 0.38/0.58    ~! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0))),
% 0.38/0.58    inference(negated_conjecture,[],[f5])).
% 0.38/0.58  fof(f5,conjecture,(
% 0.38/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0))),
% 0.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).
% 0.38/0.58  fof(f19,plain,(
% 0.38/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))) )),
% 0.38/0.58    inference(cnf_transformation,[],[f12])).
% 0.38/0.58  fof(f12,plain,(
% 0.38/0.58    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.38/0.58    inference(ennf_transformation,[],[f4])).
% 0.38/0.58  fof(f4,axiom,(
% 0.38/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.38/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).
% 0.38/0.58  fof(f14,plain,(
% 0.38/0.58    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)),
% 0.38/0.58    inference(cnf_transformation,[],[f9])).
% 0.38/0.58  % SZS output end Proof for theBenchmark
% 0.38/0.58  % (16576)------------------------------
% 0.38/0.58  % (16576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.58  % (16576)Termination reason: Refutation
% 0.38/0.58  
% 0.38/0.58  % (16576)Memory used [KB]: 10490
% 0.38/0.58  % (16576)Time elapsed: 0.003 s
% 0.38/0.58  % (16576)------------------------------
% 0.38/0.58  % (16576)------------------------------
% 0.38/0.58  % (16415)Success in time 0.222 s
%------------------------------------------------------------------------------
