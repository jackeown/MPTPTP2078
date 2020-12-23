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
% DateTime   : Thu Dec  3 12:54:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 480 expanded)
%              Number of leaves         :   18 ( 101 expanded)
%              Depth                    :   19
%              Number of atoms          :  221 (1379 expanded)
%              Number of equality atoms :   55 ( 163 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f497,plain,(
    $false ),
    inference(resolution,[],[f488,f213])).

fof(f213,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f211,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f76,f53])).

fof(f53,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

% (3650)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f211,plain,(
    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(global_subsumption,[],[f49,f50,f210])).

fof(f210,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f207,f151])).

fof(f151,plain,(
    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(global_subsumption,[],[f49,f50,f150])).

fof(f150,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f71,f52])).

fof(f52,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f207,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f75,f99])).

fof(f99,plain,(
    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f67,f51])).

fof(f51,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f488,plain,(
    ! [X10,X11] : r1_tarski(k3_xboole_0(X10,X11),X11) ),
    inference(forward_demodulation,[],[f487,f91])).

fof(f91,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f66,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f487,plain,(
    ! [X10,X11] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X10,X11)),X11) ),
    inference(forward_demodulation,[],[f481,f91])).

fof(f481,plain,(
    ! [X10,X11] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X10,X11)),k2_xboole_0(k1_xboole_0,X11)) ),
    inference(superposition,[],[f74,f475])).

% (3665)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
fof(f475,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0) ),
    inference(global_subsumption,[],[f82,f474])).

fof(f474,plain,(
    ! [X7] :
      ( k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f473,f200])).

fof(f200,plain,(
    ! [X4] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f199,f146])).

fof(f146,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f106,f85])).

fof(f85,plain,(
    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f82,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f106,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f105,f90])).

fof(f90,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f89,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f89,plain,(
    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(global_subsumption,[],[f49,f88])).

fof(f88,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f61,f79])).

fof(f79,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f55,f49])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f105,plain,(
    k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f57,f82])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f199,plain,(
    ! [X4] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f127,f133])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(global_subsumption,[],[f54,f82,f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f63,f90])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f127,plain,(
    ! [X4] : k2_relat_1(k7_relat_1(k1_xboole_0,X4)) = k9_relat_1(k1_xboole_0,X4) ),
    inference(resolution,[],[f62,f82])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f473,plain,(
    ! [X7] :
      ( k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X7)) = k3_xboole_0(X7,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f472,f200])).

fof(f472,plain,(
    ! [X7] :
      ( k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X7)) = k3_xboole_0(X7,k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f469,f133])).

fof(f469,plain,(
    ! [X6,X7] :
      ( k9_relat_1(k7_relat_1(k1_xboole_0,X6),k10_relat_1(k7_relat_1(k1_xboole_0,X6),X7)) = k3_xboole_0(X7,k9_relat_1(k7_relat_1(k1_xboole_0,X6),k1_relat_1(k7_relat_1(k1_xboole_0,X6))))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f158,f102])).

fof(f102,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(global_subsumption,[],[f49,f50,f101])).

fof(f101,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f70,f79])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f158,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(k7_relat_1(X1,X2),k10_relat_1(k7_relat_1(X1,X2),X3)) = k3_xboole_0(X3,k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))))
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f60,f155])).

fof(f155,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(k7_relat_1(X1,X2))
      | k9_relat_1(k7_relat_1(X1,X2),k10_relat_1(k7_relat_1(X1,X2),X3)) = k3_xboole_0(X3,k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f68,f70])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f82,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(global_subsumption,[],[f49,f81])).

fof(f81,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f60,f79])).

fof(f74,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (3651)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.47  % (3659)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.49  % (3654)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (3644)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (3642)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (3645)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (3643)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (3646)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (3655)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (3647)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.51  % (3661)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (3660)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.51  % (3656)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (3664)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (3658)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (3649)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (3663)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (3652)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.52  % (3648)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.52  % (3654)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f497,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(resolution,[],[f488,f213])).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1)),
% 0.20/0.52    inference(resolution,[],[f211,f111])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK0,X0)) )),
% 0.20/0.52    inference(resolution,[],[f76,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ~r1_tarski(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f22])).
% 0.20/0.52  % (3650)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  fof(f22,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.52    inference(negated_conjecture,[],[f21])).
% 0.20/0.52  fof(f21,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.52  fof(f211,plain,(
% 0.20/0.52    r1_tarski(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.52    inference(global_subsumption,[],[f49,f50,f210])).
% 0.20/0.52  fof(f210,plain,(
% 0.20/0.52    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f207,f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.20/0.52    inference(global_subsumption,[],[f49,f50,f150])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.20/0.52    inference(resolution,[],[f71,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.52  fof(f207,plain,(
% 0.20/0.52    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(superposition,[],[f75,f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.52    inference(resolution,[],[f67,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    v1_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    v1_relat_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f488,plain,(
% 0.20/0.52    ( ! [X10,X11] : (r1_tarski(k3_xboole_0(X10,X11),X11)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f487,f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.52    inference(resolution,[],[f66,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.52  fof(f487,plain,(
% 0.20/0.52    ( ! [X10,X11] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X10,X11)),X11)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f481,f91])).
% 0.20/0.52  fof(f481,plain,(
% 0.20/0.52    ( ! [X10,X11] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X10,X11)),k2_xboole_0(k1_xboole_0,X11))) )),
% 0.20/0.52    inference(superposition,[],[f74,f475])).
% 0.20/0.52  % (3665)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.52  fof(f475,plain,(
% 0.20/0.52    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0)) )),
% 0.20/0.52    inference(global_subsumption,[],[f82,f474])).
% 0.20/0.52  fof(f474,plain,(
% 0.20/0.52    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f473,f200])).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    ( ! [X4] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X4)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f199,f146])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(forward_demodulation,[],[f106,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f82,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(forward_demodulation,[],[f105,f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f89,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.20/0.52    inference(global_subsumption,[],[f49,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(superposition,[],[f61,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f55,f49])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f57,f82])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    ( ! [X4] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X4)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f127,f133])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(global_subsumption,[],[f54,f82,f131])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(superposition,[],[f63,f90])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X4] : (k2_relat_1(k7_relat_1(k1_xboole_0,X4)) = k9_relat_1(k1_xboole_0,X4)) )),
% 0.20/0.52    inference(resolution,[],[f62,f82])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.52  fof(f473,plain,(
% 0.20/0.52    ( ! [X7] : (k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X7)) = k3_xboole_0(X7,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f472,f200])).
% 0.20/0.52  fof(f472,plain,(
% 0.20/0.52    ( ! [X7] : (k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,X7)) = k3_xboole_0(X7,k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f469,f133])).
% 0.20/0.52  fof(f469,plain,(
% 0.20/0.52    ( ! [X6,X7] : (k9_relat_1(k7_relat_1(k1_xboole_0,X6),k10_relat_1(k7_relat_1(k1_xboole_0,X6),X7)) = k3_xboole_0(X7,k9_relat_1(k7_relat_1(k1_xboole_0,X6),k1_relat_1(k7_relat_1(k1_xboole_0,X6)))) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.52    inference(resolution,[],[f158,f102])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    v1_funct_1(k1_xboole_0)),
% 0.20/0.52    inference(global_subsumption,[],[f49,f50,f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    v1_funct_1(k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(superposition,[],[f70,f79])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    ( ! [X2,X3,X1] : (~v1_funct_1(X1) | k9_relat_1(k7_relat_1(X1,X2),k10_relat_1(k7_relat_1(X1,X2),X3)) = k3_xboole_0(X3,k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(global_subsumption,[],[f60,f155])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    ( ! [X2,X3,X1] : (~v1_relat_1(k7_relat_1(X1,X2)) | k9_relat_1(k7_relat_1(X1,X2),k10_relat_1(k7_relat_1(X1,X2),X3)) = k3_xboole_0(X3,k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(resolution,[],[f68,f70])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    v1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(global_subsumption,[],[f49,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(superposition,[],[f60,f79])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (3654)------------------------------
% 0.20/0.52  % (3654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3654)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (3654)Memory used [KB]: 11385
% 0.20/0.52  % (3654)Time elapsed: 0.115 s
% 0.20/0.52  % (3654)------------------------------
% 0.20/0.52  % (3654)------------------------------
% 0.20/0.52  % (3657)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.52  % (3662)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.52  % (3653)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.54  % (3641)Success in time 0.183 s
%------------------------------------------------------------------------------
