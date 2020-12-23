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
% DateTime   : Thu Dec  3 12:49:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  74 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :   37 ( 132 expanded)
%              Number of equality atoms :   26 (  75 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,(
    k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f12,f122])).

fof(f122,plain,(
    ! [X0,X1] : k3_xboole_0(k8_relat_1(X1,sK2),k8_relat_1(X0,sK2)) = k8_relat_1(k3_xboole_0(X1,X0),sK2) ),
    inference(backward_demodulation,[],[f56,f121])).

fof(f121,plain,(
    ! [X2,X3] : k3_xboole_0(k8_relat_1(X2,sK2),k2_zfmisc_1(k1_relat_1(sK2),X3)) = k8_relat_1(k3_xboole_0(X2,X3),sK2) ),
    inference(forward_demodulation,[],[f116,f21])).

fof(f21,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k3_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),X0)) ),
    inference(unit_resulting_resolution,[],[f11,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(k3_xboole_0(X0,X1),X2) != k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
        & v1_relat_1(X2) )
   => ( k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(k3_xboole_0(X0,X1),X2) != k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_relat_1)).

fof(f116,plain,(
    ! [X2,X3] : k3_xboole_0(k8_relat_1(X2,sK2),k2_zfmisc_1(k1_relat_1(sK2),X3)) = k3_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f23,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(k1_relat_1(sK2),X0),X1)) = k3_xboole_0(k8_relat_1(X0,sK2),X1) ),
    inference(superposition,[],[f14,f21])).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(k8_relat_1(X1,sK2),k2_zfmisc_1(k1_relat_1(sK2),X0)) = k3_xboole_0(k8_relat_1(X1,sK2),k8_relat_1(X0,sK2)) ),
    inference(superposition,[],[f43,f21])).

fof(f43,plain,(
    ! [X8,X9] : k3_xboole_0(k8_relat_1(X8,sK2),k3_xboole_0(sK2,X9)) = k3_xboole_0(k8_relat_1(X8,sK2),X9) ),
    inference(forward_demodulation,[],[f29,f23])).

fof(f29,plain,(
    ! [X8,X9] : k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(k1_relat_1(sK2),X8),X9)) = k3_xboole_0(k8_relat_1(X8,sK2),k3_xboole_0(sK2,X9)) ),
    inference(superposition,[],[f15,f21])).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).

fof(f12,plain,(
    k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (739803137)
% 0.13/0.36  ipcrm: permission denied for id (741376002)
% 0.13/0.36  ipcrm: permission denied for id (745013251)
% 0.13/0.37  ipcrm: permission denied for id (741441540)
% 0.13/0.37  ipcrm: permission denied for id (739868677)
% 0.13/0.37  ipcrm: permission denied for id (745078791)
% 0.13/0.37  ipcrm: permission denied for id (745111560)
% 0.13/0.37  ipcrm: permission denied for id (747110409)
% 0.13/0.37  ipcrm: permission denied for id (745177098)
% 0.13/0.37  ipcrm: permission denied for id (745209867)
% 0.13/0.38  ipcrm: permission denied for id (741670924)
% 0.13/0.38  ipcrm: permission denied for id (747143181)
% 0.13/0.38  ipcrm: permission denied for id (739966990)
% 0.13/0.38  ipcrm: permission denied for id (745275407)
% 0.20/0.38  ipcrm: permission denied for id (741769232)
% 0.20/0.38  ipcrm: permission denied for id (741834769)
% 0.20/0.38  ipcrm: permission denied for id (747175954)
% 0.20/0.38  ipcrm: permission denied for id (745340947)
% 0.20/0.38  ipcrm: permission denied for id (739999764)
% 0.20/0.39  ipcrm: permission denied for id (741933077)
% 0.20/0.39  ipcrm: permission denied for id (745373718)
% 0.20/0.39  ipcrm: permission denied for id (741998615)
% 0.20/0.39  ipcrm: permission denied for id (742031384)
% 0.20/0.39  ipcrm: permission denied for id (740065305)
% 0.20/0.39  ipcrm: permission denied for id (747208730)
% 0.20/0.39  ipcrm: permission denied for id (745439259)
% 0.20/0.39  ipcrm: permission denied for id (742129692)
% 0.20/0.40  ipcrm: permission denied for id (745472029)
% 0.20/0.40  ipcrm: permission denied for id (742195230)
% 0.20/0.40  ipcrm: permission denied for id (745504799)
% 0.20/0.40  ipcrm: permission denied for id (747274273)
% 0.20/0.40  ipcrm: permission denied for id (742326306)
% 0.20/0.41  ipcrm: permission denied for id (745701414)
% 0.20/0.41  ipcrm: permission denied for id (745734183)
% 0.20/0.41  ipcrm: permission denied for id (745766952)
% 0.20/0.41  ipcrm: permission denied for id (742555689)
% 0.20/0.41  ipcrm: permission denied for id (742588458)
% 0.20/0.41  ipcrm: permission denied for id (740294699)
% 0.20/0.41  ipcrm: permission denied for id (745799724)
% 0.20/0.41  ipcrm: permission denied for id (747405357)
% 0.20/0.42  ipcrm: permission denied for id (745865262)
% 0.20/0.42  ipcrm: permission denied for id (742752304)
% 0.20/0.42  ipcrm: permission denied for id (742817842)
% 0.20/0.42  ipcrm: permission denied for id (742850611)
% 0.20/0.42  ipcrm: permission denied for id (742883380)
% 0.20/0.42  ipcrm: permission denied for id (745963573)
% 0.20/0.43  ipcrm: permission denied for id (742948918)
% 0.20/0.43  ipcrm: permission denied for id (745996343)
% 0.20/0.43  ipcrm: permission denied for id (740425785)
% 0.20/0.43  ipcrm: permission denied for id (743047226)
% 0.20/0.43  ipcrm: permission denied for id (740458555)
% 0.20/0.43  ipcrm: permission denied for id (743079996)
% 0.20/0.44  ipcrm: permission denied for id (747569214)
% 0.20/0.44  ipcrm: permission denied for id (746127423)
% 0.20/0.44  ipcrm: permission denied for id (743211072)
% 0.20/0.44  ipcrm: permission denied for id (743243841)
% 0.20/0.44  ipcrm: permission denied for id (746160194)
% 0.20/0.44  ipcrm: permission denied for id (740556868)
% 0.20/0.44  ipcrm: permission denied for id (743342149)
% 0.20/0.44  ipcrm: permission denied for id (746225734)
% 0.20/0.45  ipcrm: permission denied for id (743407687)
% 0.20/0.45  ipcrm: permission denied for id (740589640)
% 0.20/0.45  ipcrm: permission denied for id (743440457)
% 0.20/0.45  ipcrm: permission denied for id (747634762)
% 0.20/0.45  ipcrm: permission denied for id (746291275)
% 0.20/0.45  ipcrm: permission denied for id (743571533)
% 0.20/0.45  ipcrm: permission denied for id (746356814)
% 0.20/0.46  ipcrm: permission denied for id (743637071)
% 0.20/0.46  ipcrm: permission denied for id (743702609)
% 0.20/0.46  ipcrm: permission denied for id (746422354)
% 0.20/0.46  ipcrm: permission denied for id (743768147)
% 0.20/0.46  ipcrm: permission denied for id (746455124)
% 0.20/0.46  ipcrm: permission denied for id (746487893)
% 0.20/0.46  ipcrm: permission denied for id (747765846)
% 0.20/0.47  ipcrm: permission denied for id (743931992)
% 0.20/0.47  ipcrm: permission denied for id (747864153)
% 0.20/0.47  ipcrm: permission denied for id (743997530)
% 0.20/0.47  ipcrm: permission denied for id (744030299)
% 0.20/0.47  ipcrm: permission denied for id (744063068)
% 0.20/0.47  ipcrm: permission denied for id (747896925)
% 0.20/0.47  ipcrm: permission denied for id (747929694)
% 0.20/0.47  ipcrm: permission denied for id (746684511)
% 0.20/0.48  ipcrm: permission denied for id (744194144)
% 0.20/0.48  ipcrm: permission denied for id (744226913)
% 0.20/0.48  ipcrm: permission denied for id (747962466)
% 0.20/0.48  ipcrm: permission denied for id (746750051)
% 0.20/0.48  ipcrm: permission denied for id (744325220)
% 0.20/0.48  ipcrm: permission denied for id (744390757)
% 0.20/0.48  ipcrm: permission denied for id (747995238)
% 0.20/0.48  ipcrm: permission denied for id (740819047)
% 0.20/0.49  ipcrm: permission denied for id (740851816)
% 0.20/0.49  ipcrm: permission denied for id (744456297)
% 0.20/0.49  ipcrm: permission denied for id (744489066)
% 0.20/0.49  ipcrm: permission denied for id (740917355)
% 0.20/0.49  ipcrm: permission denied for id (740950124)
% 0.20/0.49  ipcrm: permission denied for id (744521837)
% 0.20/0.49  ipcrm: permission denied for id (744554606)
% 0.20/0.49  ipcrm: permission denied for id (744587375)
% 0.20/0.49  ipcrm: permission denied for id (744620144)
% 0.20/0.50  ipcrm: permission denied for id (746815601)
% 0.20/0.50  ipcrm: permission denied for id (740982899)
% 0.20/0.50  ipcrm: permission denied for id (744783989)
% 0.20/0.50  ipcrm: permission denied for id (748093558)
% 0.20/0.50  ipcrm: permission denied for id (741048440)
% 0.20/0.51  ipcrm: permission denied for id (748159097)
% 0.20/0.51  ipcrm: permission denied for id (744915066)
% 0.20/0.51  ipcrm: permission denied for id (741146747)
% 0.20/0.51  ipcrm: permission denied for id (741212284)
% 0.20/0.51  ipcrm: permission denied for id (741245053)
% 0.20/0.51  ipcrm: permission denied for id (741277822)
% 0.20/0.56  % (28865)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.57  % (28865)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f170,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f164])).
% 0.20/0.57  fof(f164,plain,(
% 0.20/0.57    k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2)),
% 0.20/0.57    inference(superposition,[],[f12,f122])).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(k8_relat_1(X1,sK2),k8_relat_1(X0,sK2)) = k8_relat_1(k3_xboole_0(X1,X0),sK2)) )),
% 0.20/0.57    inference(backward_demodulation,[],[f56,f121])).
% 0.20/0.57  fof(f121,plain,(
% 0.20/0.57    ( ! [X2,X3] : (k3_xboole_0(k8_relat_1(X2,sK2),k2_zfmisc_1(k1_relat_1(sK2),X3)) = k8_relat_1(k3_xboole_0(X2,X3),sK2)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f116,f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ( ! [X0] : (k8_relat_1(X0,sK2) = k3_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),X0))) )),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f11,f13])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,plain,(
% 0.20/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).
% 0.20/0.57  fof(f11,plain,(
% 0.20/0.57    v1_relat_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,plain,(
% 0.20/0.57    k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) & v1_relat_1(sK2)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).
% 0.20/0.57  fof(f9,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (k8_relat_1(k3_xboole_0(X0,X1),X2) != k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & v1_relat_1(X2)) => (k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) & v1_relat_1(sK2))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f7,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (k8_relat_1(k3_xboole_0(X0,X1),X2) != k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & v1_relat_1(X2))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)))),
% 0.20/0.57    inference(negated_conjecture,[],[f5])).
% 0.20/0.57  fof(f5,conjecture,(
% 0.20/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_relat_1)).
% 0.20/0.57  fof(f116,plain,(
% 0.20/0.57    ( ! [X2,X3] : (k3_xboole_0(k8_relat_1(X2,sK2),k2_zfmisc_1(k1_relat_1(sK2),X3)) = k3_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k3_xboole_0(X2,X3)))) )),
% 0.20/0.57    inference(superposition,[],[f23,f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(k1_relat_1(sK2),X0),X1)) = k3_xboole_0(k8_relat_1(X0,sK2),X1)) )),
% 0.20/0.57    inference(superposition,[],[f14,f21])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(k8_relat_1(X1,sK2),k2_zfmisc_1(k1_relat_1(sK2),X0)) = k3_xboole_0(k8_relat_1(X1,sK2),k8_relat_1(X0,sK2))) )),
% 0.20/0.57    inference(superposition,[],[f43,f21])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ( ! [X8,X9] : (k3_xboole_0(k8_relat_1(X8,sK2),k3_xboole_0(sK2,X9)) = k3_xboole_0(k8_relat_1(X8,sK2),X9)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f29,f23])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ( ! [X8,X9] : (k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(k1_relat_1(sK2),X8),X9)) = k3_xboole_0(k8_relat_1(X8,sK2),k3_xboole_0(sK2,X9))) )),
% 0.20/0.57    inference(superposition,[],[f15,f21])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).
% 0.20/0.57  fof(f12,plain,(
% 0.20/0.57    k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),
% 0.20/0.57    inference(cnf_transformation,[],[f10])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (28865)------------------------------
% 0.20/0.57  % (28865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (28865)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (28865)Memory used [KB]: 6268
% 0.20/0.57  % (28865)Time elapsed: 0.007 s
% 0.20/0.57  % (28865)------------------------------
% 0.20/0.57  % (28865)------------------------------
% 0.20/0.57  % (28729)Success in time 0.218 s
%------------------------------------------------------------------------------
