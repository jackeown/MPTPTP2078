%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:45 EST 2020

% Result     : Theorem 4.25s
% Output     : Refutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 275 expanded)
%              Number of leaves         :   12 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  137 ( 564 expanded)
%              Number of equality atoms :   29 (  59 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3783,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f42,f3727])).

fof(f3727,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(forward_demodulation,[],[f3726,f78])).

fof(f78,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(f3726,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(forward_demodulation,[],[f3725,f478])).

fof(f478,plain,(
    ! [X2,X3] : k9_relat_1(k8_relat_1(X2,sK2),X3) = k3_xboole_0(k9_relat_1(sK2,X3),X2) ),
    inference(superposition,[],[f139,f100])).

fof(f100,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1) ),
    inference(unit_resulting_resolution,[],[f75,f52])).

fof(f75,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f139,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k3_xboole_0(k9_relat_1(sK2,X1),X0) ),
    inference(forward_demodulation,[],[f138,f86])).

fof(f86,plain,(
    ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK2),X1) = k8_relat_1(X0,k7_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f41,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f138,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X1),X0) ),
    inference(forward_demodulation,[],[f122,f78])).

fof(f122,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X1)),X0) ),
    inference(unit_resulting_resolution,[],[f76,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f76,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f3725,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k9_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),X0)) ),
    inference(forward_demodulation,[],[f3713,f100])).

fof(f3713,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k2_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),X0))) ),
    inference(unit_resulting_resolution,[],[f76,f98,f3546,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f3546,plain,(
    ! [X19,X20] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X20,X19)),k7_relat_1(k8_relat_1(k9_relat_1(sK2,X19),sK2),X20)) ),
    inference(superposition,[],[f208,f816])).

fof(f816,plain,(
    ! [X0,X1] : k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),k3_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f304,f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK2,X0),X1)
      | k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(X1,sK2),X0) ) ),
    inference(forward_demodulation,[],[f219,f86])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK2,X0),X1)
      | k7_relat_1(sK2,X0) = k8_relat_1(X1,k7_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f216,f76])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK2,X0),X1)
      | k7_relat_1(sK2,X0) = k8_relat_1(X1,k7_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f54,f78])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f304,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X1)) ),
    inference(forward_demodulation,[],[f303,f78])).

fof(f303,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k9_relat_1(sK2,X1)) ),
    inference(forward_demodulation,[],[f301,f78])).

fof(f301,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k2_relat_1(k7_relat_1(sK2,X1))) ),
    inference(unit_resulting_resolution,[],[f76,f76,f150,f44])).

fof(f150,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(sK2,k3_xboole_0(X0,X1)),k7_relat_1(sK2,X1)) ),
    inference(forward_demodulation,[],[f146,f87])).

fof(f87,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f41,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f146,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k7_relat_1(sK2,X0),X1),k7_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f41,f76,f77,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(f77,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f41,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f208,plain,(
    ! [X2,X0,X1] : r1_tarski(k7_relat_1(k8_relat_1(X0,sK2),k3_xboole_0(X1,X2)),k7_relat_1(k8_relat_1(X0,sK2),X1)) ),
    inference(forward_demodulation,[],[f185,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1),X2) = k7_relat_1(k8_relat_1(X0,sK2),k3_xboole_0(X1,X2)) ),
    inference(unit_resulting_resolution,[],[f75,f63])).

fof(f185,plain,(
    ! [X2,X0,X1] : r1_tarski(k7_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1),X2),k7_relat_1(k8_relat_1(X0,sK2),X1)) ),
    inference(unit_resulting_resolution,[],[f98,f51])).

fof(f98,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) ),
    inference(unit_resulting_resolution,[],[f75,f50])).

fof(f42,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.16/0.35  % Computer   : n022.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % WCLimit    : 600
% 0.16/0.35  % DateTime   : Tue Dec  1 11:29:56 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.22/0.51  % (1073)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.51  % (1065)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (1070)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (1069)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (1066)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (1082)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (1068)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (1100)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (1100)Refutation not found, incomplete strategy% (1100)------------------------------
% 0.22/0.53  % (1100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (1100)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (1100)Memory used [KB]: 1663
% 0.22/0.53  % (1100)Time elapsed: 0.113 s
% 0.22/0.53  % (1100)------------------------------
% 0.22/0.53  % (1100)------------------------------
% 0.22/0.53  % (1064)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (1091)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (1080)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (1092)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (1090)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (1089)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (1079)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (1095)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (1078)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (1072)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (1093)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (1077)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (1076)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (1071)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (1067)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (1074)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (1097)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (1097)Refutation not found, incomplete strategy% (1097)------------------------------
% 0.22/0.55  % (1097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1097)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1097)Memory used [KB]: 10746
% 0.22/0.55  % (1097)Time elapsed: 0.130 s
% 0.22/0.55  % (1097)------------------------------
% 0.22/0.55  % (1097)------------------------------
% 0.22/0.55  % (1081)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (1096)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (1080)Refutation not found, incomplete strategy% (1080)------------------------------
% 0.22/0.55  % (1080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1080)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1080)Memory used [KB]: 10618
% 0.22/0.55  % (1080)Time elapsed: 0.140 s
% 0.22/0.55  % (1080)------------------------------
% 0.22/0.55  % (1080)------------------------------
% 0.22/0.56  % (1094)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (1075)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (1083)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (1074)Refutation not found, incomplete strategy% (1074)------------------------------
% 0.22/0.57  % (1074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (1074)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (1074)Memory used [KB]: 10746
% 0.22/0.57  % (1074)Time elapsed: 0.152 s
% 0.22/0.57  % (1074)------------------------------
% 0.22/0.57  % (1074)------------------------------
% 2.07/0.67  % (1067)Refutation not found, incomplete strategy% (1067)------------------------------
% 2.07/0.67  % (1067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.68  % (1067)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.68  
% 2.07/0.68  % (1067)Memory used [KB]: 6140
% 2.07/0.68  % (1067)Time elapsed: 0.235 s
% 2.07/0.68  % (1067)------------------------------
% 2.07/0.68  % (1067)------------------------------
% 2.07/0.68  % (1113)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.07/0.68  % (1114)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.07/0.69  % (1114)Refutation not found, incomplete strategy% (1114)------------------------------
% 2.07/0.69  % (1114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.69  % (1114)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.69  
% 2.07/0.69  % (1114)Memory used [KB]: 6268
% 2.07/0.69  % (1114)Time elapsed: 0.104 s
% 2.07/0.69  % (1114)------------------------------
% 2.07/0.69  % (1114)------------------------------
% 2.07/0.70  % (1112)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.59/0.71  % (1115)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.01/0.79  % (1118)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.01/0.81  % (1093)Time limit reached!
% 3.01/0.81  % (1093)------------------------------
% 3.01/0.81  % (1093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.81  % (1093)Termination reason: Time limit
% 3.01/0.81  % (1093)Termination phase: Saturation
% 3.01/0.81  
% 3.01/0.81  % (1093)Memory used [KB]: 13176
% 3.01/0.81  % (1093)Time elapsed: 0.400 s
% 3.01/0.81  % (1093)------------------------------
% 3.01/0.81  % (1093)------------------------------
% 3.01/0.82  % (1121)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.01/0.85  % (1066)Time limit reached!
% 3.01/0.85  % (1066)------------------------------
% 3.01/0.85  % (1066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.85  % (1066)Termination reason: Time limit
% 3.01/0.85  
% 3.01/0.85  % (1066)Memory used [KB]: 8059
% 3.01/0.85  % (1066)Time elapsed: 0.427 s
% 3.01/0.85  % (1066)------------------------------
% 3.01/0.85  % (1066)------------------------------
% 3.94/0.93  % (1078)Time limit reached!
% 3.94/0.93  % (1078)------------------------------
% 3.94/0.93  % (1078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.94/0.93  % (1078)Termination reason: Time limit
% 3.94/0.93  
% 3.94/0.93  % (1078)Memory used [KB]: 4861
% 3.94/0.93  % (1078)Time elapsed: 0.513 s
% 3.94/0.93  % (1078)------------------------------
% 3.94/0.93  % (1078)------------------------------
% 4.25/0.95  % (1070)Time limit reached!
% 4.25/0.95  % (1070)------------------------------
% 4.25/0.95  % (1070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.95  % (1070)Termination reason: Time limit
% 4.25/0.95  % (1070)Termination phase: Saturation
% 4.25/0.95  
% 4.25/0.95  % (1070)Memory used [KB]: 14967
% 4.25/0.95  % (1070)Time elapsed: 0.500 s
% 4.25/0.95  % (1070)------------------------------
% 4.25/0.95  % (1070)------------------------------
% 4.25/0.95  % (1180)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.25/0.97  % (1115)Refutation found. Thanks to Tanya!
% 4.25/0.97  % SZS status Theorem for theBenchmark
% 4.25/0.97  % SZS output start Proof for theBenchmark
% 4.25/0.97  fof(f3783,plain,(
% 4.25/0.97    $false),
% 4.25/0.97    inference(unit_resulting_resolution,[],[f42,f3727])).
% 4.25/0.97  fof(f3727,plain,(
% 4.25/0.97    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 4.25/0.97    inference(forward_demodulation,[],[f3726,f78])).
% 4.25/0.97  fof(f78,plain,(
% 4.25/0.97    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 4.25/0.97    inference(unit_resulting_resolution,[],[f41,f52])).
% 4.25/0.97  fof(f52,plain,(
% 4.25/0.97    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 4.25/0.97    inference(cnf_transformation,[],[f28])).
% 4.25/0.97  fof(f28,plain,(
% 4.25/0.97    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.25/0.97    inference(ennf_transformation,[],[f16])).
% 4.25/0.97  fof(f16,axiom,(
% 4.25/0.97    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 4.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 4.25/0.97  fof(f41,plain,(
% 4.25/0.97    v1_relat_1(sK2)),
% 4.25/0.97    inference(cnf_transformation,[],[f37])).
% 4.25/0.97  fof(f37,plain,(
% 4.25/0.97    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 4.25/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f36])).
% 4.25/0.97  fof(f36,plain,(
% 4.25/0.97    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 4.25/0.97    introduced(choice_axiom,[])).
% 4.25/0.97  fof(f21,plain,(
% 4.25/0.97    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 4.25/0.97    inference(ennf_transformation,[],[f20])).
% 4.25/0.97  fof(f20,negated_conjecture,(
% 4.25/0.97    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 4.25/0.97    inference(negated_conjecture,[],[f19])).
% 4.25/0.97  fof(f19,conjecture,(
% 4.25/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 4.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).
% 4.25/0.97  fof(f3726,plain,(
% 4.25/0.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 4.25/0.97    inference(forward_demodulation,[],[f3725,f478])).
% 4.25/0.97  fof(f478,plain,(
% 4.25/0.97    ( ! [X2,X3] : (k9_relat_1(k8_relat_1(X2,sK2),X3) = k3_xboole_0(k9_relat_1(sK2,X3),X2)) )),
% 4.25/0.97    inference(superposition,[],[f139,f100])).
% 4.25/0.97  fof(f100,plain,(
% 4.25/0.97    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1)) )),
% 4.25/0.97    inference(unit_resulting_resolution,[],[f75,f52])).
% 4.25/0.97  fof(f75,plain,(
% 4.25/0.97    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) )),
% 4.25/0.97    inference(unit_resulting_resolution,[],[f41,f49])).
% 4.25/0.97  fof(f49,plain,(
% 4.25/0.97    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 4.25/0.97    inference(cnf_transformation,[],[f25])).
% 4.25/0.97  fof(f25,plain,(
% 4.25/0.97    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 4.25/0.97    inference(ennf_transformation,[],[f10])).
% 4.25/0.97  fof(f10,axiom,(
% 4.25/0.97    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 4.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 4.25/0.97  fof(f139,plain,(
% 4.25/0.97    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k3_xboole_0(k9_relat_1(sK2,X1),X0)) )),
% 4.25/0.97    inference(forward_demodulation,[],[f138,f86])).
% 4.25/0.97  fof(f86,plain,(
% 4.25/0.97    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,sK2),X1) = k8_relat_1(X0,k7_relat_1(sK2,X1))) )),
% 4.25/0.97    inference(unit_resulting_resolution,[],[f41,f62])).
% 4.25/0.97  fof(f62,plain,(
% 4.25/0.97    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) )),
% 4.25/0.97    inference(cnf_transformation,[],[f34])).
% 4.25/0.97  fof(f34,plain,(
% 4.25/0.97    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 4.25/0.97    inference(ennf_transformation,[],[f15])).
% 4.25/0.97  fof(f15,axiom,(
% 4.25/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 4.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 4.25/0.97  fof(f138,plain,(
% 4.25/0.97    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X1),X0)) )),
% 4.25/0.97    inference(forward_demodulation,[],[f122,f78])).
% 4.25/0.97  fof(f122,plain,(
% 4.25/0.97    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X1)),X0)) )),
% 4.25/0.97    inference(unit_resulting_resolution,[],[f76,f53])).
% 4.25/0.97  fof(f53,plain,(
% 4.25/0.97    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) )),
% 4.25/0.97    inference(cnf_transformation,[],[f29])).
% 4.25/0.97  fof(f29,plain,(
% 4.25/0.97    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.25/0.97    inference(ennf_transformation,[],[f13])).
% 4.25/0.97  fof(f13,axiom,(
% 4.25/0.97    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 4.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 4.25/0.97  fof(f76,plain,(
% 4.25/0.97    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 4.25/0.97    inference(unit_resulting_resolution,[],[f41,f50])).
% 4.25/0.97  fof(f50,plain,(
% 4.25/0.97    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.25/0.97    inference(cnf_transformation,[],[f26])).
% 4.25/0.97  fof(f26,plain,(
% 4.25/0.97    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.25/0.97    inference(ennf_transformation,[],[f9])).
% 4.25/0.97  fof(f9,axiom,(
% 4.25/0.97    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 4.25/0.98  fof(f3725,plain,(
% 4.25/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k9_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),X0))) )),
% 4.25/0.98    inference(forward_demodulation,[],[f3713,f100])).
% 4.25/0.98  fof(f3713,plain,(
% 4.25/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k2_relat_1(k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),X0)))) )),
% 4.25/0.98    inference(unit_resulting_resolution,[],[f76,f98,f3546,f44])).
% 4.25/0.98  fof(f44,plain,(
% 4.25/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.25/0.98    inference(cnf_transformation,[],[f23])).
% 4.25/0.98  fof(f23,plain,(
% 4.25/0.98    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.25/0.98    inference(flattening,[],[f22])).
% 4.25/0.98  fof(f22,plain,(
% 4.25/0.98    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.25/0.98    inference(ennf_transformation,[],[f17])).
% 4.25/0.98  fof(f17,axiom,(
% 4.25/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 4.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 4.25/0.98  fof(f3546,plain,(
% 4.25/0.98    ( ! [X19,X20] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X20,X19)),k7_relat_1(k8_relat_1(k9_relat_1(sK2,X19),sK2),X20))) )),
% 4.25/0.98    inference(superposition,[],[f208,f816])).
% 4.25/0.98  fof(f816,plain,(
% 4.25/0.98    ( ! [X0,X1] : (k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k8_relat_1(k9_relat_1(sK2,X1),sK2),k3_xboole_0(X0,X1))) )),
% 4.25/0.98    inference(unit_resulting_resolution,[],[f304,f220])).
% 4.25/0.98  fof(f220,plain,(
% 4.25/0.98    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK2,X0),X1) | k7_relat_1(sK2,X0) = k7_relat_1(k8_relat_1(X1,sK2),X0)) )),
% 4.25/0.98    inference(forward_demodulation,[],[f219,f86])).
% 4.25/0.98  fof(f219,plain,(
% 4.25/0.98    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK2,X0),X1) | k7_relat_1(sK2,X0) = k8_relat_1(X1,k7_relat_1(sK2,X0))) )),
% 4.25/0.98    inference(subsumption_resolution,[],[f216,f76])).
% 4.25/0.98  fof(f216,plain,(
% 4.25/0.98    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK2,X0),X1) | k7_relat_1(sK2,X0) = k8_relat_1(X1,k7_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 4.25/0.98    inference(superposition,[],[f54,f78])).
% 4.25/0.98  fof(f54,plain,(
% 4.25/0.98    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 4.25/0.98    inference(cnf_transformation,[],[f31])).
% 4.25/0.98  fof(f31,plain,(
% 4.25/0.98    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.25/0.98    inference(flattening,[],[f30])).
% 4.25/0.98  fof(f30,plain,(
% 4.25/0.98    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.25/0.98    inference(ennf_transformation,[],[f14])).
% 4.25/0.98  fof(f14,axiom,(
% 4.25/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 4.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 4.25/0.98  fof(f304,plain,(
% 4.25/0.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X1))) )),
% 4.25/0.98    inference(forward_demodulation,[],[f303,f78])).
% 4.25/0.98  fof(f303,plain,(
% 4.25/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k9_relat_1(sK2,X1))) )),
% 4.25/0.98    inference(forward_demodulation,[],[f301,f78])).
% 4.25/0.98  fof(f301,plain,(
% 4.25/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k2_relat_1(k7_relat_1(sK2,X1)))) )),
% 4.25/0.98    inference(unit_resulting_resolution,[],[f76,f76,f150,f44])).
% 4.25/0.98  fof(f150,plain,(
% 4.25/0.98    ( ! [X0,X1] : (r1_tarski(k7_relat_1(sK2,k3_xboole_0(X0,X1)),k7_relat_1(sK2,X1))) )),
% 4.25/0.98    inference(forward_demodulation,[],[f146,f87])).
% 4.25/0.98  fof(f87,plain,(
% 4.25/0.98    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 4.25/0.98    inference(unit_resulting_resolution,[],[f41,f63])).
% 4.25/0.98  fof(f63,plain,(
% 4.25/0.98    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 4.25/0.98    inference(cnf_transformation,[],[f35])).
% 4.25/0.98  fof(f35,plain,(
% 4.25/0.98    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 4.25/0.98    inference(ennf_transformation,[],[f11])).
% 4.25/0.98  fof(f11,axiom,(
% 4.25/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 4.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 4.25/0.98  fof(f146,plain,(
% 4.25/0.98    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(sK2,X0),X1),k7_relat_1(sK2,X1))) )),
% 4.25/0.98    inference(unit_resulting_resolution,[],[f41,f76,f77,f55])).
% 4.25/0.98  fof(f55,plain,(
% 4.25/0.98    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 4.25/0.98    inference(cnf_transformation,[],[f33])).
% 4.25/0.98  fof(f33,plain,(
% 4.25/0.98    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.25/0.98    inference(flattening,[],[f32])).
% 4.25/0.98  fof(f32,plain,(
% 4.25/0.98    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.25/0.98    inference(ennf_transformation,[],[f12])).
% 4.25/0.98  fof(f12,axiom,(
% 4.25/0.98    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 4.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 4.25/0.98  fof(f77,plain,(
% 4.25/0.98    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK2)) )),
% 4.25/0.98    inference(unit_resulting_resolution,[],[f41,f51])).
% 4.25/0.98  fof(f51,plain,(
% 4.25/0.98    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 4.25/0.98    inference(cnf_transformation,[],[f27])).
% 4.25/0.98  fof(f27,plain,(
% 4.25/0.98    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 4.25/0.98    inference(ennf_transformation,[],[f18])).
% 4.25/0.98  fof(f18,axiom,(
% 4.25/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 4.25/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 4.25/0.98  fof(f208,plain,(
% 4.25/0.98    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k8_relat_1(X0,sK2),k3_xboole_0(X1,X2)),k7_relat_1(k8_relat_1(X0,sK2),X1))) )),
% 4.25/0.98    inference(forward_demodulation,[],[f185,f109])).
% 4.25/0.98  fof(f109,plain,(
% 4.25/0.98    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1),X2) = k7_relat_1(k8_relat_1(X0,sK2),k3_xboole_0(X1,X2))) )),
% 4.25/0.98    inference(unit_resulting_resolution,[],[f75,f63])).
% 4.25/0.98  fof(f185,plain,(
% 4.25/0.98    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1),X2),k7_relat_1(k8_relat_1(X0,sK2),X1))) )),
% 4.25/0.98    inference(unit_resulting_resolution,[],[f98,f51])).
% 4.25/0.98  fof(f98,plain,(
% 4.25/0.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1))) )),
% 4.25/0.98    inference(unit_resulting_resolution,[],[f75,f50])).
% 4.25/0.98  fof(f42,plain,(
% 4.25/0.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 4.25/0.98    inference(cnf_transformation,[],[f37])).
% 4.25/0.98  % SZS output end Proof for theBenchmark
% 4.25/0.98  % (1115)------------------------------
% 4.25/0.98  % (1115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.98  % (1115)Termination reason: Refutation
% 4.25/0.98  
% 4.25/0.98  % (1115)Memory used [KB]: 13432
% 4.25/0.98  % (1115)Time elapsed: 0.381 s
% 4.25/0.98  % (1115)------------------------------
% 4.25/0.98  % (1115)------------------------------
% 4.25/0.98  % (1062)Success in time 0.599 s
%------------------------------------------------------------------------------
