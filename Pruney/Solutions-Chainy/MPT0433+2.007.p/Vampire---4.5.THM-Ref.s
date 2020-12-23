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
% DateTime   : Thu Dec  3 12:46:52 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   50 (  87 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 206 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(subsumption_resolution,[],[f133,f59])).

fof(f59,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f133,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f132,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f132,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f129,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f88,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f66,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f66,plain,(
    ! [X4,X5] :
      ( r1_tarski(k1_relat_1(X4),k1_relat_1(k2_xboole_0(X4,X5)))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f31,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f129,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f128,f69])).

fof(f69,plain,(
    ! [X6,X5] : r1_tarski(k3_xboole_0(X6,X5),X5) ),
    inference(superposition,[],[f59,f55])).

fof(f55,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f45,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f128,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f124,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f124,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    inference(resolution,[],[f90,f61])).

fof(f61,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:44:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (801472512)
% 0.21/0.37  ipcrm: permission denied for id (801505282)
% 0.21/0.37  ipcrm: permission denied for id (805437443)
% 0.21/0.37  ipcrm: permission denied for id (805470212)
% 0.21/0.37  ipcrm: permission denied for id (801538053)
% 0.21/0.38  ipcrm: permission denied for id (801636360)
% 0.21/0.38  ipcrm: permission denied for id (805568521)
% 0.21/0.38  ipcrm: permission denied for id (801701898)
% 0.21/0.38  ipcrm: permission denied for id (805601291)
% 0.21/0.38  ipcrm: permission denied for id (805666829)
% 0.21/0.39  ipcrm: permission denied for id (805732367)
% 0.21/0.39  ipcrm: permission denied for id (805797905)
% 0.21/0.39  ipcrm: permission denied for id (801898514)
% 0.21/0.39  ipcrm: permission denied for id (801931283)
% 0.21/0.39  ipcrm: permission denied for id (801964052)
% 0.21/0.39  ipcrm: permission denied for id (801996821)
% 0.21/0.39  ipcrm: permission denied for id (802029590)
% 0.21/0.40  ipcrm: permission denied for id (805896217)
% 0.21/0.40  ipcrm: permission denied for id (805928986)
% 0.21/0.40  ipcrm: permission denied for id (805994524)
% 0.21/0.41  ipcrm: permission denied for id (802390049)
% 0.21/0.41  ipcrm: permission denied for id (802455587)
% 0.21/0.41  ipcrm: permission denied for id (802488356)
% 0.21/0.41  ipcrm: permission denied for id (802521125)
% 0.21/0.41  ipcrm: permission denied for id (806191142)
% 0.21/0.42  ipcrm: permission denied for id (802586663)
% 0.21/0.42  ipcrm: permission denied for id (802619432)
% 0.21/0.42  ipcrm: permission denied for id (802652201)
% 0.21/0.42  ipcrm: permission denied for id (802750507)
% 0.21/0.42  ipcrm: permission denied for id (802783276)
% 0.21/0.43  ipcrm: permission denied for id (802881583)
% 0.21/0.43  ipcrm: permission denied for id (806354992)
% 0.21/0.43  ipcrm: permission denied for id (806387761)
% 0.21/0.43  ipcrm: permission denied for id (802979890)
% 0.21/0.43  ipcrm: permission denied for id (803045428)
% 0.21/0.43  ipcrm: permission denied for id (806453301)
% 0.21/0.43  ipcrm: permission denied for id (803110966)
% 0.21/0.44  ipcrm: permission denied for id (803143735)
% 0.21/0.44  ipcrm: permission denied for id (806486072)
% 0.21/0.44  ipcrm: permission denied for id (806551610)
% 0.21/0.44  ipcrm: permission denied for id (803307580)
% 0.21/0.44  ipcrm: permission denied for id (803340349)
% 0.21/0.44  ipcrm: permission denied for id (803373118)
% 0.21/0.45  ipcrm: permission denied for id (803405887)
% 0.21/0.45  ipcrm: permission denied for id (803471424)
% 0.21/0.45  ipcrm: permission denied for id (803536962)
% 0.21/0.45  ipcrm: permission denied for id (803569731)
% 0.21/0.45  ipcrm: permission denied for id (803602500)
% 0.21/0.45  ipcrm: permission denied for id (806649925)
% 0.21/0.46  ipcrm: permission denied for id (803733575)
% 0.21/0.46  ipcrm: permission denied for id (806715464)
% 0.21/0.46  ipcrm: permission denied for id (803799113)
% 0.21/0.46  ipcrm: permission denied for id (803864651)
% 0.21/0.46  ipcrm: permission denied for id (803897420)
% 0.21/0.46  ipcrm: permission denied for id (806781005)
% 0.21/0.47  ipcrm: permission denied for id (803995727)
% 0.21/0.47  ipcrm: permission denied for id (806846544)
% 0.21/0.47  ipcrm: permission denied for id (804061265)
% 0.21/0.47  ipcrm: permission denied for id (804094034)
% 0.21/0.47  ipcrm: permission denied for id (804126803)
% 0.21/0.47  ipcrm: permission denied for id (804159572)
% 0.21/0.47  ipcrm: permission denied for id (804192341)
% 0.21/0.47  ipcrm: permission denied for id (804225110)
% 0.21/0.48  ipcrm: permission denied for id (804257879)
% 0.21/0.48  ipcrm: permission denied for id (806912089)
% 0.21/0.48  ipcrm: permission denied for id (806944858)
% 0.21/0.48  ipcrm: permission denied for id (804388955)
% 0.21/0.48  ipcrm: permission denied for id (806977628)
% 0.21/0.48  ipcrm: permission denied for id (804487262)
% 0.21/0.49  ipcrm: permission denied for id (804552801)
% 0.21/0.49  ipcrm: permission denied for id (807108706)
% 0.21/0.49  ipcrm: permission denied for id (807141475)
% 0.21/0.49  ipcrm: permission denied for id (804651108)
% 0.21/0.49  ipcrm: permission denied for id (807174245)
% 0.21/0.49  ipcrm: permission denied for id (804716646)
% 0.21/0.50  ipcrm: permission denied for id (804814953)
% 0.21/0.50  ipcrm: permission denied for id (804847722)
% 0.21/0.50  ipcrm: permission denied for id (804913260)
% 0.21/0.50  ipcrm: permission denied for id (804946029)
% 0.21/0.50  ipcrm: permission denied for id (807305326)
% 0.21/0.51  ipcrm: permission denied for id (805011568)
% 0.21/0.51  ipcrm: permission denied for id (807403633)
% 0.21/0.51  ipcrm: permission denied for id (807436402)
% 0.21/0.51  ipcrm: permission denied for id (807567477)
% 0.21/0.51  ipcrm: permission denied for id (807600246)
% 0.21/0.52  ipcrm: permission denied for id (807633015)
% 0.21/0.52  ipcrm: permission denied for id (807698553)
% 0.21/0.52  ipcrm: permission denied for id (807731322)
% 0.21/0.52  ipcrm: permission denied for id (807796860)
% 0.21/0.52  ipcrm: permission denied for id (807829629)
% 0.21/0.52  ipcrm: permission denied for id (807895166)
% 0.21/0.53  ipcrm: permission denied for id (807927935)
% 0.61/0.60  % (1381)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.61/0.60  % (1381)Refutation found. Thanks to Tanya!
% 0.61/0.60  % SZS status Theorem for theBenchmark
% 0.61/0.60  % SZS output start Proof for theBenchmark
% 0.61/0.60  fof(f134,plain,(
% 0.61/0.60    $false),
% 0.61/0.60    inference(subsumption_resolution,[],[f133,f59])).
% 0.61/0.60  fof(f59,plain,(
% 0.61/0.60    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 0.61/0.60    inference(superposition,[],[f32,f37])).
% 0.61/0.60  fof(f37,plain,(
% 0.61/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.61/0.60    inference(cnf_transformation,[],[f4])).
% 0.61/0.60  fof(f4,axiom,(
% 0.61/0.60    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.61/0.60  fof(f32,plain,(
% 0.61/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.61/0.60    inference(cnf_transformation,[],[f3])).
% 0.61/0.60  fof(f3,axiom,(
% 0.61/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.61/0.60  fof(f133,plain,(
% 0.61/0.60    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 0.61/0.60    inference(subsumption_resolution,[],[f132,f26])).
% 0.61/0.60  fof(f26,plain,(
% 0.61/0.60    v1_relat_1(sK0)),
% 0.61/0.60    inference(cnf_transformation,[],[f24])).
% 0.61/0.60  fof(f24,plain,(
% 0.61/0.60    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.61/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f23,f22])).
% 0.61/0.60  fof(f22,plain,(
% 0.61/0.60    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.61/0.60    introduced(choice_axiom,[])).
% 0.61/0.60  fof(f23,plain,(
% 0.61/0.60    ? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.61/0.60    introduced(choice_axiom,[])).
% 0.61/0.60  fof(f16,plain,(
% 0.61/0.60    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.61/0.60    inference(ennf_transformation,[],[f15])).
% 0.61/0.60  fof(f15,negated_conjecture,(
% 0.61/0.60    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.61/0.60    inference(negated_conjecture,[],[f14])).
% 0.61/0.60  fof(f14,conjecture,(
% 0.61/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 0.61/0.60  fof(f132,plain,(
% 0.61/0.60    ~v1_relat_1(sK0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 0.61/0.60    inference(resolution,[],[f129,f90])).
% 0.61/0.60  fof(f90,plain,(
% 0.61/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1)) )),
% 0.61/0.60    inference(subsumption_resolution,[],[f88,f44])).
% 0.61/0.60  fof(f44,plain,(
% 0.61/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.61/0.60    inference(resolution,[],[f30,f40])).
% 0.61/0.60  fof(f40,plain,(
% 0.61/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.61/0.60    inference(cnf_transformation,[],[f25])).
% 0.61/0.60  fof(f25,plain,(
% 0.61/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.61/0.60    inference(nnf_transformation,[],[f11])).
% 0.61/0.60  fof(f11,axiom,(
% 0.61/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.61/0.60  fof(f30,plain,(
% 0.61/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.61/0.60    inference(cnf_transformation,[],[f18])).
% 0.61/0.60  fof(f18,plain,(
% 0.61/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.61/0.60    inference(ennf_transformation,[],[f12])).
% 0.61/0.60  fof(f12,axiom,(
% 0.61/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.61/0.60  fof(f88,plain,(
% 0.61/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(X0,X1)) )),
% 0.61/0.60    inference(superposition,[],[f66,f38])).
% 0.61/0.60  fof(f38,plain,(
% 0.61/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.61/0.60    inference(cnf_transformation,[],[f19])).
% 0.61/0.60  fof(f19,plain,(
% 0.61/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.61/0.60    inference(ennf_transformation,[],[f1])).
% 0.61/0.60  fof(f1,axiom,(
% 0.61/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.61/0.60  fof(f66,plain,(
% 0.61/0.60    ( ! [X4,X5] : (r1_tarski(k1_relat_1(X4),k1_relat_1(k2_xboole_0(X4,X5))) | ~v1_relat_1(X5) | ~v1_relat_1(X4)) )),
% 0.61/0.60    inference(superposition,[],[f31,f29])).
% 0.61/0.60  fof(f29,plain,(
% 0.61/0.60    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.61/0.60    inference(cnf_transformation,[],[f17])).
% 0.61/0.60  fof(f17,plain,(
% 0.61/0.60    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.61/0.60    inference(ennf_transformation,[],[f13])).
% 0.61/0.60  fof(f13,axiom,(
% 0.61/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).
% 0.61/0.60  fof(f31,plain,(
% 0.61/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.61/0.60    inference(cnf_transformation,[],[f5])).
% 0.61/0.60  fof(f5,axiom,(
% 0.61/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.61/0.60  fof(f129,plain,(
% 0.61/0.60    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 0.61/0.60    inference(subsumption_resolution,[],[f128,f69])).
% 0.61/0.60  fof(f69,plain,(
% 0.61/0.60    ( ! [X6,X5] : (r1_tarski(k3_xboole_0(X6,X5),X5)) )),
% 0.61/0.60    inference(superposition,[],[f59,f55])).
% 0.61/0.60  fof(f55,plain,(
% 0.61/0.60    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.61/0.60    inference(superposition,[],[f45,f34])).
% 0.61/0.60  fof(f34,plain,(
% 0.61/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.61/0.60    inference(cnf_transformation,[],[f10])).
% 0.61/0.60  fof(f10,axiom,(
% 0.61/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.61/0.60  fof(f45,plain,(
% 0.61/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.61/0.60    inference(superposition,[],[f34,f33])).
% 0.61/0.60  fof(f33,plain,(
% 0.61/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.61/0.60    inference(cnf_transformation,[],[f6])).
% 0.61/0.60  fof(f6,axiom,(
% 0.61/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.61/0.60  fof(f128,plain,(
% 0.61/0.60    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 0.61/0.60    inference(subsumption_resolution,[],[f124,f27])).
% 0.61/0.60  fof(f27,plain,(
% 0.61/0.60    v1_relat_1(sK1)),
% 0.61/0.60    inference(cnf_transformation,[],[f24])).
% 0.61/0.60  fof(f124,plain,(
% 0.61/0.60    ~v1_relat_1(sK1) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 0.61/0.60    inference(resolution,[],[f90,f61])).
% 0.61/0.60  fof(f61,plain,(
% 0.61/0.60    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 0.61/0.60    inference(resolution,[],[f42,f28])).
% 0.61/0.60  fof(f28,plain,(
% 0.61/0.60    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 0.61/0.60    inference(cnf_transformation,[],[f24])).
% 0.61/0.60  fof(f42,plain,(
% 0.61/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.61/0.60    inference(cnf_transformation,[],[f21])).
% 0.61/0.60  fof(f21,plain,(
% 0.61/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.61/0.60    inference(flattening,[],[f20])).
% 0.61/0.60  fof(f20,plain,(
% 0.61/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.61/0.60    inference(ennf_transformation,[],[f2])).
% 0.61/0.61  fof(f2,axiom,(
% 0.61/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.61/0.61  % SZS output end Proof for theBenchmark
% 0.61/0.61  % (1381)------------------------------
% 0.61/0.61  % (1381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.61/0.61  % (1381)Termination reason: Refutation
% 0.61/0.61  
% 0.61/0.61  % (1381)Memory used [KB]: 1663
% 0.61/0.61  % (1381)Time elapsed: 0.008 s
% 0.61/0.61  % (1381)------------------------------
% 0.61/0.61  % (1381)------------------------------
% 0.61/0.61  % (1238)Success in time 0.246 s
%------------------------------------------------------------------------------
