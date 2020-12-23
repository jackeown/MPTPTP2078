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
% DateTime   : Thu Dec  3 12:51:22 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   24 (  60 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 296 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f18])).

fof(f18,plain,(
    ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    & r1_tarski(sK2,sK1)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
          & r1_tarski(X2,sK1)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
        & r1_tarski(X2,sK1)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
      & r1_tarski(sK2,sK1)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( r1_tarski(X2,X1)
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( r1_tarski(X2,X1)
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t210_relat_1)).

fof(f28,plain,(
    r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f23,f21])).

fof(f21,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f15,f16,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f16,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f15,f14,f17,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f17,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:11:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.35  ipcrm: permission denied for id (809795584)
% 0.13/0.35  ipcrm: permission denied for id (809828354)
% 0.13/0.35  ipcrm: permission denied for id (809861123)
% 0.13/0.36  ipcrm: permission denied for id (809893892)
% 0.13/0.36  ipcrm: permission denied for id (809959430)
% 0.13/0.36  ipcrm: permission denied for id (809992200)
% 0.13/0.36  ipcrm: permission denied for id (813826057)
% 0.13/0.36  ipcrm: permission denied for id (810057738)
% 0.13/0.37  ipcrm: permission denied for id (810123276)
% 0.13/0.37  ipcrm: permission denied for id (810156045)
% 0.13/0.37  ipcrm: permission denied for id (810254351)
% 0.13/0.37  ipcrm: permission denied for id (810287120)
% 0.13/0.37  ipcrm: permission denied for id (813924369)
% 0.13/0.37  ipcrm: permission denied for id (810352658)
% 0.13/0.37  ipcrm: permission denied for id (810385427)
% 0.13/0.38  ipcrm: permission denied for id (810418196)
% 0.13/0.38  ipcrm: permission denied for id (810483734)
% 0.13/0.38  ipcrm: permission denied for id (813989911)
% 0.13/0.38  ipcrm: permission denied for id (814055449)
% 0.13/0.38  ipcrm: permission denied for id (814088218)
% 0.13/0.39  ipcrm: permission denied for id (810680348)
% 0.13/0.39  ipcrm: permission denied for id (810713117)
% 0.13/0.39  ipcrm: permission denied for id (810745886)
% 0.13/0.39  ipcrm: permission denied for id (810778655)
% 0.13/0.39  ipcrm: permission denied for id (810811424)
% 0.13/0.39  ipcrm: permission denied for id (814153761)
% 0.20/0.39  ipcrm: permission denied for id (810876963)
% 0.20/0.40  ipcrm: permission denied for id (814219300)
% 0.20/0.40  ipcrm: permission denied for id (810942501)
% 0.20/0.40  ipcrm: permission denied for id (810975270)
% 0.20/0.40  ipcrm: permission denied for id (814284840)
% 0.20/0.40  ipcrm: permission denied for id (811073577)
% 0.20/0.40  ipcrm: permission denied for id (811106347)
% 0.20/0.41  ipcrm: permission denied for id (811139116)
% 0.20/0.41  ipcrm: permission denied for id (814383150)
% 0.20/0.41  ipcrm: permission denied for id (811204655)
% 0.20/0.41  ipcrm: permission denied for id (814514227)
% 0.20/0.42  ipcrm: permission denied for id (811368500)
% 0.20/0.42  ipcrm: permission denied for id (811434038)
% 0.20/0.42  ipcrm: permission denied for id (814612536)
% 0.20/0.42  ipcrm: permission denied for id (814645305)
% 0.20/0.42  ipcrm: permission denied for id (811565114)
% 0.20/0.42  ipcrm: permission denied for id (814678075)
% 0.20/0.43  ipcrm: permission denied for id (814710844)
% 0.20/0.43  ipcrm: permission denied for id (814776382)
% 0.20/0.43  ipcrm: permission denied for id (814809151)
% 0.20/0.43  ipcrm: permission denied for id (811761728)
% 0.20/0.43  ipcrm: permission denied for id (811827266)
% 0.20/0.43  ipcrm: permission denied for id (811860035)
% 0.20/0.44  ipcrm: permission denied for id (811892804)
% 0.20/0.44  ipcrm: permission denied for id (814940231)
% 0.20/0.44  ipcrm: permission denied for id (811991112)
% 0.20/0.44  ipcrm: permission denied for id (812056650)
% 0.20/0.45  ipcrm: permission denied for id (812122188)
% 0.20/0.45  ipcrm: permission denied for id (812154957)
% 0.20/0.45  ipcrm: permission denied for id (812187726)
% 0.20/0.45  ipcrm: permission denied for id (812220495)
% 0.20/0.45  ipcrm: permission denied for id (812253264)
% 0.20/0.45  ipcrm: permission denied for id (812286033)
% 0.20/0.45  ipcrm: permission denied for id (815038546)
% 0.20/0.45  ipcrm: permission denied for id (812351571)
% 0.20/0.46  ipcrm: permission denied for id (812384340)
% 0.20/0.46  ipcrm: permission denied for id (815071317)
% 0.20/0.46  ipcrm: permission denied for id (812449878)
% 0.20/0.46  ipcrm: permission denied for id (815104087)
% 0.20/0.46  ipcrm: permission denied for id (812515416)
% 0.20/0.46  ipcrm: permission denied for id (815136857)
% 0.20/0.46  ipcrm: permission denied for id (812613722)
% 0.20/0.46  ipcrm: permission denied for id (812646491)
% 0.20/0.47  ipcrm: permission denied for id (815267935)
% 0.20/0.47  ipcrm: permission denied for id (815333473)
% 0.20/0.47  ipcrm: permission denied for id (815399011)
% 0.20/0.48  ipcrm: permission denied for id (812941412)
% 0.20/0.48  ipcrm: permission denied for id (813105256)
% 0.20/0.48  ipcrm: permission denied for id (815595627)
% 0.20/0.48  ipcrm: permission denied for id (815628396)
% 0.20/0.49  ipcrm: permission denied for id (815661165)
% 0.20/0.49  ipcrm: permission denied for id (815726703)
% 0.20/0.49  ipcrm: permission denied for id (815792241)
% 0.20/0.49  ipcrm: permission denied for id (813367410)
% 0.20/0.49  ipcrm: permission denied for id (813400179)
% 0.20/0.49  ipcrm: permission denied for id (815825012)
% 0.20/0.50  ipcrm: permission denied for id (813432949)
% 0.20/0.50  ipcrm: permission denied for id (813465718)
% 0.20/0.50  ipcrm: permission denied for id (815857783)
% 0.20/0.50  ipcrm: permission denied for id (815890552)
% 0.20/0.50  ipcrm: permission denied for id (815956090)
% 0.20/0.51  ipcrm: permission denied for id (816087166)
% 0.20/0.51  ipcrm: permission denied for id (813695103)
% 0.36/0.55  % (31730)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.36/0.55  % (31730)Refutation found. Thanks to Tanya!
% 0.36/0.55  % SZS status Theorem for theBenchmark
% 0.36/0.55  % SZS output start Proof for theBenchmark
% 0.36/0.55  fof(f29,plain,(
% 0.36/0.55    $false),
% 0.36/0.55    inference(subsumption_resolution,[],[f28,f18])).
% 0.36/0.55  fof(f18,plain,(
% 0.36/0.55    ~r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.36/0.55    inference(cnf_transformation,[],[f13])).
% 0.36/0.55  fof(f13,plain,(
% 0.36/0.55    (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).
% 0.36/0.55  fof(f11,plain,(
% 0.36/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.36/0.55    introduced(choice_axiom,[])).
% 0.36/0.55  fof(f12,plain,(
% 0.36/0.55    ? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) => (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.36/0.55    introduced(choice_axiom,[])).
% 0.36/0.55  fof(f6,plain,(
% 0.36/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.36/0.55    inference(flattening,[],[f5])).
% 0.36/0.55  fof(f5,plain,(
% 0.36/0.55    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1)) & (v4_relat_1(X2,X0) & v1_relat_1(X2))) & v1_relat_1(X1))),
% 0.36/0.55    inference(ennf_transformation,[],[f4])).
% 0.36/0.55  fof(f4,negated_conjecture,(
% 0.36/0.55    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => (r1_tarski(X2,X1) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.36/0.55    inference(negated_conjecture,[],[f3])).
% 0.36/0.55  fof(f3,conjecture,(
% 0.36/0.55    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => (r1_tarski(X2,X1) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t210_relat_1)).
% 0.36/0.55  fof(f28,plain,(
% 0.36/0.55    r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.36/0.55    inference(superposition,[],[f23,f21])).
% 0.36/0.55  fof(f21,plain,(
% 0.36/0.55    sK2 = k7_relat_1(sK2,sK0)),
% 0.36/0.55    inference(unit_resulting_resolution,[],[f15,f16,f20])).
% 0.36/0.55  fof(f20,plain,(
% 0.36/0.55    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.36/0.55    inference(cnf_transformation,[],[f10])).
% 0.36/0.55  fof(f10,plain,(
% 0.36/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.36/0.55    inference(flattening,[],[f9])).
% 0.36/0.55  fof(f9,plain,(
% 0.36/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.36/0.55    inference(ennf_transformation,[],[f2])).
% 0.36/0.55  fof(f2,axiom,(
% 0.36/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.36/0.55  fof(f16,plain,(
% 0.36/0.55    v4_relat_1(sK2,sK0)),
% 0.36/0.55    inference(cnf_transformation,[],[f13])).
% 0.36/0.55  fof(f15,plain,(
% 0.36/0.55    v1_relat_1(sK2)),
% 0.36/0.55    inference(cnf_transformation,[],[f13])).
% 0.36/0.55  fof(f23,plain,(
% 0.36/0.55    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK1,X0))) )),
% 0.36/0.55    inference(unit_resulting_resolution,[],[f15,f14,f17,f19])).
% 0.36/0.55  fof(f19,plain,(
% 0.36/0.55    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.36/0.55    inference(cnf_transformation,[],[f8])).
% 0.36/0.55  fof(f8,plain,(
% 0.36/0.55    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.36/0.55    inference(flattening,[],[f7])).
% 0.36/0.55  fof(f7,plain,(
% 0.36/0.55    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.36/0.55    inference(ennf_transformation,[],[f1])).
% 0.36/0.55  fof(f1,axiom,(
% 0.36/0.55    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.36/0.55  fof(f17,plain,(
% 0.36/0.55    r1_tarski(sK2,sK1)),
% 0.36/0.55    inference(cnf_transformation,[],[f13])).
% 0.36/0.55  fof(f14,plain,(
% 0.36/0.55    v1_relat_1(sK1)),
% 0.36/0.55    inference(cnf_transformation,[],[f13])).
% 0.36/0.55  % SZS output end Proof for theBenchmark
% 0.36/0.55  % (31730)------------------------------
% 0.36/0.55  % (31730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.55  % (31730)Termination reason: Refutation
% 0.36/0.55  
% 0.36/0.55  % (31730)Memory used [KB]: 6012
% 0.36/0.55  % (31730)Time elapsed: 0.003 s
% 0.36/0.55  % (31730)------------------------------
% 0.36/0.55  % (31730)------------------------------
% 0.36/0.55  % (31594)Success in time 0.21 s
%------------------------------------------------------------------------------
