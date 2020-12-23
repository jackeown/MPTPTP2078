%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:04 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 159 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  190 ( 438 expanded)
%              Number of equality atoms :   33 (  36 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f434,plain,(
    $false ),
    inference(subsumption_resolution,[],[f433,f113])).

fof(f113,plain,(
    ! [X1] : r1_tarski(k3_xboole_0(k2_relat_1(sK2),X1),X1) ),
    inference(backward_demodulation,[],[f61,f63])).

fof(f63,plain,(
    ! [X3] : k2_relat_1(k8_relat_1(X3,sK2)) = k3_xboole_0(k2_relat_1(sK2),X3) ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

fof(f61,plain,(
    ! [X1] : r1_tarski(k2_relat_1(k8_relat_1(X1,sK2)),X1) ),
    inference(resolution,[],[f39,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f433,plain,(
    ~ r1_tarski(k3_xboole_0(k2_relat_1(sK2),sK1),sK1) ),
    inference(forward_demodulation,[],[f418,f144])).

fof(f144,plain,(
    ! [X1] : k3_xboole_0(k2_relat_1(sK2),X1) = k9_relat_1(sK2,k10_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f143,f39])).

fof(f143,plain,(
    ! [X1] :
      ( k3_xboole_0(k2_relat_1(sK2),X1) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f142,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f142,plain,(
    ! [X1] :
      ( k3_xboole_0(k2_relat_1(sK2),X1) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f141,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f141,plain,(
    ! [X1] :
      ( k3_xboole_0(k2_relat_1(sK2),X1) = k9_relat_1(sK2,k10_relat_1(sK2,X1))
      | ~ r1_tarski(k3_xboole_0(k2_relat_1(sK2),X1),k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f48,f64])).

fof(f64,plain,(
    ! [X4] : k10_relat_1(sK2,X4) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X4)) ),
    inference(resolution,[],[f39,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f418,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) ),
    inference(resolution,[],[f372,f258])).

fof(f258,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(subsumption_resolution,[],[f257,f39])).

fof(f257,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f256,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f256,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f251,f42])).

fof(f251,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK0)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f70])).

fof(f70,plain,(
    ! [X17,X15,X16] :
      ( r1_tarski(k9_relat_1(X15,X16),k9_relat_1(sK2,X17))
      | ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X15,sK2)
      | ~ v1_relat_1(X15) ) ),
    inference(resolution,[],[f39,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(f73,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(resolution,[],[f41,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f41,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f372,plain,(
    ! [X14,X12,X13] :
      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X12,X13)),X14)
      | ~ r1_tarski(k9_relat_1(sK2,X13),X14) ) ),
    inference(resolution,[],[f344,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f344,plain,(
    ! [X6,X7] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X6,X7)),k9_relat_1(sK2,X7)) ),
    inference(backward_demodulation,[],[f66,f169])).

fof(f169,plain,(
    ! [X12,X11] : k9_relat_1(k7_relat_1(sK2,X11),X12) = k9_relat_1(sK2,k3_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f168,f62])).

fof(f62,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f168,plain,(
    ! [X12,X11] : k9_relat_1(k7_relat_1(sK2,X11),X12) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X11,X12))) ),
    inference(subsumption_resolution,[],[f160,f60])).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f39,f43])).

% (30020)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (30019)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (30030)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (30010)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (30035)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f160,plain,(
    ! [X12,X11] :
      ( k9_relat_1(k7_relat_1(sK2,X11),X12) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X11,X12)))
      | ~ v1_relat_1(k7_relat_1(sK2,X11)) ) ),
    inference(superposition,[],[f45,f68])).

fof(f68,plain,(
    ! [X10,X11] : k7_relat_1(k7_relat_1(sK2,X10),X11) = k7_relat_1(sK2,k3_xboole_0(X10,X11)) ),
    inference(resolution,[],[f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f66,plain,(
    ! [X6,X7] : r1_tarski(k9_relat_1(k7_relat_1(sK2,X6),X7),k9_relat_1(sK2,X7)) ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:53:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (30034)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (30013)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.55  % (30016)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (30028)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (30021)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (30012)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.55  % (30033)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (30022)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.44/0.55  % (30029)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.44/0.55  % (30031)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.44/0.55  % (30015)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.44/0.55  % (30024)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.44/0.55  % (30011)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.55  % (30017)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.44/0.55  % (30032)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.44/0.55  % (30014)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.44/0.56  % (30026)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.44/0.56  % (30027)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.44/0.56  % (30025)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.44/0.56  % (30023)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.44/0.56  % (30018)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.59/0.57  % (30028)Refutation found. Thanks to Tanya!
% 1.59/0.57  % SZS status Theorem for theBenchmark
% 1.59/0.57  % SZS output start Proof for theBenchmark
% 1.59/0.57  fof(f434,plain,(
% 1.59/0.57    $false),
% 1.59/0.57    inference(subsumption_resolution,[],[f433,f113])).
% 1.59/0.57  fof(f113,plain,(
% 1.59/0.57    ( ! [X1] : (r1_tarski(k3_xboole_0(k2_relat_1(sK2),X1),X1)) )),
% 1.59/0.57    inference(backward_demodulation,[],[f61,f63])).
% 1.59/0.57  fof(f63,plain,(
% 1.59/0.57    ( ! [X3] : (k2_relat_1(k8_relat_1(X3,sK2)) = k3_xboole_0(k2_relat_1(sK2),X3)) )),
% 1.59/0.57    inference(resolution,[],[f39,f46])).
% 1.59/0.57  fof(f46,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f22])).
% 1.59/0.57  fof(f22,plain,(
% 1.59/0.57    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f8])).
% 1.59/0.57  fof(f8,axiom,(
% 1.59/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 1.59/0.57  fof(f39,plain,(
% 1.59/0.57    v1_relat_1(sK2)),
% 1.59/0.57    inference(cnf_transformation,[],[f36])).
% 1.59/0.57  fof(f36,plain,(
% 1.59/0.57    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.59/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35])).
% 1.59/0.57  fof(f35,plain,(
% 1.59/0.57    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.59/0.57    introduced(choice_axiom,[])).
% 1.59/0.57  fof(f18,plain,(
% 1.59/0.57    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.59/0.57    inference(flattening,[],[f17])).
% 1.59/0.57  fof(f17,plain,(
% 1.59/0.57    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.59/0.57    inference(ennf_transformation,[],[f16])).
% 1.59/0.57  fof(f16,negated_conjecture,(
% 1.59/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 1.59/0.57    inference(negated_conjecture,[],[f15])).
% 1.59/0.57  fof(f15,conjecture,(
% 1.59/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).
% 1.59/0.57  fof(f61,plain,(
% 1.59/0.57    ( ! [X1] : (r1_tarski(k2_relat_1(k8_relat_1(X1,sK2)),X1)) )),
% 1.59/0.57    inference(resolution,[],[f39,f44])).
% 1.59/0.57  fof(f44,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f20])).
% 1.59/0.57  fof(f20,plain,(
% 1.59/0.57    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f7])).
% 1.59/0.57  fof(f7,axiom,(
% 1.59/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 1.59/0.57  fof(f433,plain,(
% 1.59/0.57    ~r1_tarski(k3_xboole_0(k2_relat_1(sK2),sK1),sK1)),
% 1.59/0.57    inference(forward_demodulation,[],[f418,f144])).
% 1.59/0.57  fof(f144,plain,(
% 1.59/0.57    ( ! [X1] : (k3_xboole_0(k2_relat_1(sK2),X1) = k9_relat_1(sK2,k10_relat_1(sK2,X1))) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f143,f39])).
% 1.59/0.57  fof(f143,plain,(
% 1.59/0.57    ( ! [X1] : (k3_xboole_0(k2_relat_1(sK2),X1) = k9_relat_1(sK2,k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f142,f40])).
% 1.59/0.57  fof(f40,plain,(
% 1.59/0.57    v1_funct_1(sK2)),
% 1.59/0.57    inference(cnf_transformation,[],[f36])).
% 1.59/0.57  fof(f142,plain,(
% 1.59/0.57    ( ! [X1] : (k3_xboole_0(k2_relat_1(sK2),X1) = k9_relat_1(sK2,k10_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f141,f42])).
% 1.59/0.57  fof(f42,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f2])).
% 1.59/0.57  fof(f2,axiom,(
% 1.59/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.59/0.57  fof(f141,plain,(
% 1.59/0.57    ( ! [X1] : (k3_xboole_0(k2_relat_1(sK2),X1) = k9_relat_1(sK2,k10_relat_1(sK2,X1)) | ~r1_tarski(k3_xboole_0(k2_relat_1(sK2),X1),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.59/0.57    inference(superposition,[],[f48,f64])).
% 1.59/0.57  fof(f64,plain,(
% 1.59/0.57    ( ! [X4] : (k10_relat_1(sK2,X4) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X4))) )),
% 1.59/0.57    inference(resolution,[],[f39,f47])).
% 1.59/0.57  fof(f47,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f23])).
% 1.59/0.57  fof(f23,plain,(
% 1.59/0.57    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f12])).
% 1.59/0.57  fof(f12,axiom,(
% 1.59/0.57    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.59/0.57  fof(f48,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f25])).
% 1.59/0.57  fof(f25,plain,(
% 1.59/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(flattening,[],[f24])).
% 1.59/0.57  fof(f24,plain,(
% 1.59/0.57    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.59/0.57    inference(ennf_transformation,[],[f14])).
% 1.59/0.57  fof(f14,axiom,(
% 1.59/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.59/0.57  fof(f418,plain,(
% 1.59/0.57    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)),
% 1.59/0.57    inference(resolution,[],[f372,f258])).
% 1.59/0.57  fof(f258,plain,(
% 1.59/0.57    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 1.59/0.57    inference(subsumption_resolution,[],[f257,f39])).
% 1.59/0.57  fof(f257,plain,(
% 1.59/0.57    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) | ~v1_relat_1(sK2)),
% 1.59/0.57    inference(subsumption_resolution,[],[f256,f59])).
% 1.59/0.57  fof(f59,plain,(
% 1.59/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.59/0.57    inference(equality_resolution,[],[f49])).
% 1.59/0.57  fof(f49,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.59/0.57    inference(cnf_transformation,[],[f38])).
% 1.59/0.57  fof(f38,plain,(
% 1.59/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.57    inference(flattening,[],[f37])).
% 1.59/0.57  fof(f37,plain,(
% 1.59/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.57    inference(nnf_transformation,[],[f1])).
% 1.59/0.57  fof(f1,axiom,(
% 1.59/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.59/0.57  fof(f256,plain,(
% 1.59/0.57    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2)),
% 1.59/0.57    inference(subsumption_resolution,[],[f251,f42])).
% 1.59/0.57  fof(f251,plain,(
% 1.59/0.57    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) | ~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK0) | ~r1_tarski(sK2,sK2) | ~v1_relat_1(sK2)),
% 1.59/0.57    inference(resolution,[],[f73,f70])).
% 1.59/0.57  fof(f70,plain,(
% 1.59/0.57    ( ! [X17,X15,X16] : (r1_tarski(k9_relat_1(X15,X16),k9_relat_1(sK2,X17)) | ~r1_tarski(X16,X17) | ~r1_tarski(X15,sK2) | ~v1_relat_1(X15)) )),
% 1.59/0.57    inference(resolution,[],[f39,f55])).
% 1.59/0.57  fof(f55,plain,(
% 1.59/0.57    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f30])).
% 1.59/0.57  fof(f30,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.59/0.57    inference(flattening,[],[f29])).
% 1.59/0.57  fof(f29,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.59/0.57    inference(ennf_transformation,[],[f10])).
% 1.59/0.57  fof(f10,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).
% 1.59/0.57  fof(f73,plain,(
% 1.59/0.57    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 1.59/0.57    inference(resolution,[],[f41,f57])).
% 1.59/0.57  fof(f57,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f34])).
% 1.59/0.57  fof(f34,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.59/0.57    inference(flattening,[],[f33])).
% 1.59/0.57  fof(f33,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.59/0.57    inference(ennf_transformation,[],[f3])).
% 1.59/0.57  fof(f3,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.59/0.57  fof(f41,plain,(
% 1.59/0.57    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 1.59/0.57    inference(cnf_transformation,[],[f36])).
% 1.59/0.57  fof(f372,plain,(
% 1.59/0.57    ( ! [X14,X12,X13] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X12,X13)),X14) | ~r1_tarski(k9_relat_1(sK2,X13),X14)) )),
% 1.59/0.57    inference(resolution,[],[f344,f56])).
% 1.59/0.57  fof(f56,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f32])).
% 1.59/0.57  fof(f32,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.59/0.57    inference(flattening,[],[f31])).
% 1.59/0.57  fof(f31,plain,(
% 1.59/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.59/0.57    inference(ennf_transformation,[],[f4])).
% 1.59/0.57  fof(f4,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.59/0.57  fof(f344,plain,(
% 1.59/0.57    ( ! [X6,X7] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X6,X7)),k9_relat_1(sK2,X7))) )),
% 1.59/0.57    inference(backward_demodulation,[],[f66,f169])).
% 1.59/0.57  fof(f169,plain,(
% 1.59/0.57    ( ! [X12,X11] : (k9_relat_1(k7_relat_1(sK2,X11),X12) = k9_relat_1(sK2,k3_xboole_0(X11,X12))) )),
% 1.59/0.57    inference(forward_demodulation,[],[f168,f62])).
% 1.59/0.57  fof(f62,plain,(
% 1.59/0.57    ( ! [X2] : (k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)) )),
% 1.59/0.57    inference(resolution,[],[f39,f45])).
% 1.59/0.57  fof(f45,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f21])).
% 1.59/0.57  fof(f21,plain,(
% 1.59/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f9])).
% 1.59/0.57  fof(f9,axiom,(
% 1.59/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.59/0.57  fof(f168,plain,(
% 1.59/0.57    ( ! [X12,X11] : (k9_relat_1(k7_relat_1(sK2,X11),X12) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X11,X12)))) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f160,f60])).
% 1.59/0.57  fof(f60,plain,(
% 1.59/0.57    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 1.59/0.57    inference(resolution,[],[f39,f43])).
% 1.59/0.57  % (30020)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.59/0.57  % (30019)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.59/0.57  % (30030)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.59/0.57  % (30010)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.59/0.58  % (30035)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.59/0.59  fof(f43,plain,(
% 1.59/0.59    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f19])).
% 1.59/0.59  fof(f19,plain,(
% 1.59/0.59    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f5])).
% 1.59/0.59  fof(f5,axiom,(
% 1.59/0.59    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.59/0.59  fof(f160,plain,(
% 1.59/0.59    ( ! [X12,X11] : (k9_relat_1(k7_relat_1(sK2,X11),X12) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X11,X12))) | ~v1_relat_1(k7_relat_1(sK2,X11))) )),
% 1.59/0.59    inference(superposition,[],[f45,f68])).
% 1.59/0.59  fof(f68,plain,(
% 1.59/0.59    ( ! [X10,X11] : (k7_relat_1(k7_relat_1(sK2,X10),X11) = k7_relat_1(sK2,k3_xboole_0(X10,X11))) )),
% 1.59/0.59    inference(resolution,[],[f39,f54])).
% 1.59/0.59  fof(f54,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f28])).
% 1.59/0.59  fof(f28,plain,(
% 1.59/0.59    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.59/0.59    inference(ennf_transformation,[],[f6])).
% 1.59/0.59  fof(f6,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 1.59/0.59  fof(f66,plain,(
% 1.59/0.59    ( ! [X6,X7] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X6),X7),k9_relat_1(sK2,X7))) )),
% 1.59/0.59    inference(resolution,[],[f39,f52])).
% 1.59/0.59  fof(f52,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f26])).
% 1.59/0.59  fof(f26,plain,(
% 1.59/0.59    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.59/0.59    inference(ennf_transformation,[],[f11])).
% 1.59/0.59  fof(f11,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_relat_1)).
% 1.59/0.59  % SZS output end Proof for theBenchmark
% 1.59/0.59  % (30028)------------------------------
% 1.59/0.59  % (30028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (30028)Termination reason: Refutation
% 1.59/0.59  
% 1.59/0.59  % (30028)Memory used [KB]: 1791
% 1.59/0.59  % (30028)Time elapsed: 0.141 s
% 1.59/0.59  % (30028)------------------------------
% 1.59/0.59  % (30028)------------------------------
% 1.59/0.59  % (30009)Success in time 0.218 s
%------------------------------------------------------------------------------
