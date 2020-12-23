%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:26 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 184 expanded)
%              Number of leaves         :   10 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 359 expanded)
%              Number of equality atoms :   56 ( 152 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f481,plain,(
    $false ),
    inference(subsumption_resolution,[],[f480,f156])).

fof(f156,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f37,f86])).

fof(f86,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
    inference(unit_resulting_resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f37,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f480,plain,(
    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f472,f100])).

fof(f100,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f99,f81])).

fof(f81,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f80,f54])).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f78,f55])).

fof(f55,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f51,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f99,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0 ),
    inference(forward_demodulation,[],[f93,f55])).

fof(f93,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f52,f51,f56,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f52,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f472,plain,(
    k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f371,f235])).

fof(f235,plain,(
    k10_relat_1(sK0,sK2) = k3_xboole_0(k10_relat_1(sK0,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f36,f121])).

fof(f121,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k3_xboole_0(X2,X1) = X2 ) ),
    inference(backward_demodulation,[],[f104,f120])).

fof(f120,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,X0) ),
    inference(forward_demodulation,[],[f119,f100])).

fof(f119,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) ),
    inference(forward_demodulation,[],[f116,f54])).

fof(f116,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f52,f51,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2 ) ),
    inference(forward_demodulation,[],[f103,f55])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k2_relat_1(k6_relat_1(X1)))
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2 ) ),
    inference(subsumption_resolution,[],[f97,f51])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | ~ r1_tarski(X2,k2_relat_1(k6_relat_1(X1)))
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2 ) ),
    inference(resolution,[],[f47,f52])).

fof(f36,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

% (12985)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f371,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f120,f362])).

fof(f362,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[],[f112,f81])).

fof(f112,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(forward_demodulation,[],[f111,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(unit_resulting_resolution,[],[f51,f43])).

fof(f111,plain,(
    ! [X2,X0,X1] : k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_demodulation,[],[f108,f85])).

fof(f85,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f51,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f108,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(unit_resulting_resolution,[],[f51,f51,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (12970)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.49  % (12987)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (12961)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.55  % (12980)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (12990)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.56  % (12981)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.56  % (12969)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.56  % (12967)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (12978)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.57  % (12986)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.57  % (12971)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.58/0.58  % (12963)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.58/0.58  % (12976)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.83/0.60  % (12988)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.83/0.60  % (12992)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.83/0.61  % (12974)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.83/0.61  % (12975)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.83/0.61  % (12962)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.83/0.61  % (12981)Refutation found. Thanks to Tanya!
% 1.83/0.61  % SZS status Theorem for theBenchmark
% 1.83/0.61  % SZS output start Proof for theBenchmark
% 1.83/0.61  fof(f481,plain,(
% 1.83/0.61    $false),
% 1.83/0.61    inference(subsumption_resolution,[],[f480,f156])).
% 1.83/0.61  fof(f156,plain,(
% 1.83/0.61    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.83/0.61    inference(superposition,[],[f37,f86])).
% 1.83/0.61  fof(f86,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1))) )),
% 1.83/0.61    inference(unit_resulting_resolution,[],[f38,f43])).
% 1.83/0.61  fof(f43,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.83/0.61    inference(cnf_transformation,[],[f24])).
% 1.83/0.61  fof(f24,plain,(
% 1.83/0.61    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.83/0.61    inference(ennf_transformation,[],[f16])).
% 1.83/0.61  fof(f16,axiom,(
% 1.83/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.83/0.61  fof(f38,plain,(
% 1.83/0.61    v1_relat_1(sK0)),
% 1.83/0.61    inference(cnf_transformation,[],[f23])).
% 1.83/0.61  fof(f23,plain,(
% 1.83/0.61    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.83/0.61    inference(flattening,[],[f22])).
% 1.83/0.61  fof(f22,plain,(
% 1.83/0.61    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.83/0.61    inference(ennf_transformation,[],[f21])).
% 1.83/0.61  fof(f21,negated_conjecture,(
% 1.83/0.61    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.83/0.61    inference(negated_conjecture,[],[f20])).
% 1.83/0.61  fof(f20,conjecture,(
% 1.83/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.83/0.61  fof(f37,plain,(
% 1.83/0.61    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.83/0.61    inference(cnf_transformation,[],[f23])).
% 1.83/0.61  fof(f480,plain,(
% 1.83/0.61    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.83/0.61    inference(forward_demodulation,[],[f472,f100])).
% 1.83/0.61  fof(f100,plain,(
% 1.83/0.61    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.83/0.61    inference(forward_demodulation,[],[f99,f81])).
% 1.83/0.61  fof(f81,plain,(
% 1.83/0.61    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.83/0.61    inference(forward_demodulation,[],[f80,f54])).
% 1.83/0.61  fof(f54,plain,(
% 1.83/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.83/0.61    inference(cnf_transformation,[],[f13])).
% 1.83/0.61  fof(f13,axiom,(
% 1.83/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.83/0.61  fof(f80,plain,(
% 1.83/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.83/0.61    inference(forward_demodulation,[],[f78,f55])).
% 1.83/0.61  fof(f55,plain,(
% 1.83/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.83/0.61    inference(cnf_transformation,[],[f13])).
% 1.83/0.61  fof(f78,plain,(
% 1.83/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 1.83/0.61    inference(unit_resulting_resolution,[],[f51,f50])).
% 1.83/0.61  fof(f50,plain,(
% 1.83/0.61    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f34])).
% 1.83/0.61  fof(f34,plain,(
% 1.83/0.61    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.83/0.61    inference(ennf_transformation,[],[f11])).
% 1.83/0.61  fof(f11,axiom,(
% 1.83/0.61    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.83/0.61  fof(f51,plain,(
% 1.83/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.83/0.61    inference(cnf_transformation,[],[f15])).
% 1.83/0.61  fof(f15,axiom,(
% 1.83/0.61    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.83/0.61  fof(f99,plain,(
% 1.83/0.61    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0) )),
% 1.83/0.61    inference(forward_demodulation,[],[f93,f55])).
% 1.83/0.61  fof(f93,plain,(
% 1.83/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))))) )),
% 1.83/0.61    inference(unit_resulting_resolution,[],[f52,f51,f56,f47])).
% 1.83/0.61  fof(f47,plain,(
% 1.83/0.61    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 1.83/0.61    inference(cnf_transformation,[],[f31])).
% 1.83/0.61  fof(f31,plain,(
% 1.83/0.61    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.83/0.61    inference(flattening,[],[f30])).
% 1.83/0.61  fof(f30,plain,(
% 1.83/0.61    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.83/0.61    inference(ennf_transformation,[],[f17])).
% 1.83/0.61  fof(f17,axiom,(
% 1.83/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.83/0.61  fof(f56,plain,(
% 1.83/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.83/0.61    inference(equality_resolution,[],[f41])).
% 1.83/0.61  fof(f41,plain,(
% 1.83/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.83/0.61    inference(cnf_transformation,[],[f1])).
% 1.83/0.61  fof(f1,axiom,(
% 1.83/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.83/0.61  fof(f52,plain,(
% 1.83/0.61    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.83/0.61    inference(cnf_transformation,[],[f15])).
% 1.83/0.61  fof(f472,plain,(
% 1.83/0.61    k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 1.83/0.61    inference(superposition,[],[f371,f235])).
% 1.83/0.61  fof(f235,plain,(
% 1.83/0.61    k10_relat_1(sK0,sK2) = k3_xboole_0(k10_relat_1(sK0,sK2),sK1)),
% 1.83/0.61    inference(unit_resulting_resolution,[],[f36,f121])).
% 1.83/0.61  fof(f121,plain,(
% 1.83/0.61    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k3_xboole_0(X2,X1) = X2) )),
% 1.83/0.61    inference(backward_demodulation,[],[f104,f120])).
% 1.83/0.61  fof(f120,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,X0)) )),
% 1.83/0.61    inference(forward_demodulation,[],[f119,f100])).
% 1.83/0.61  fof(f119,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))) )),
% 1.83/0.61    inference(forward_demodulation,[],[f116,f54])).
% 1.83/0.61  fof(f116,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) )),
% 1.83/0.61    inference(unit_resulting_resolution,[],[f52,f51,f49])).
% 1.83/0.61  fof(f49,plain,(
% 1.83/0.61    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 1.83/0.61    inference(cnf_transformation,[],[f33])).
% 1.83/0.61  fof(f33,plain,(
% 1.83/0.61    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.83/0.61    inference(flattening,[],[f32])).
% 1.83/0.61  fof(f32,plain,(
% 1.83/0.61    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.83/0.61    inference(ennf_transformation,[],[f18])).
% 1.83/0.61  fof(f18,axiom,(
% 1.83/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 1.83/0.61  fof(f104,plain,(
% 1.83/0.61    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2) )),
% 1.83/0.61    inference(forward_demodulation,[],[f103,f55])).
% 1.83/0.61  fof(f103,plain,(
% 1.83/0.61    ( ! [X2,X1] : (~r1_tarski(X2,k2_relat_1(k6_relat_1(X1))) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2) )),
% 1.83/0.61    inference(subsumption_resolution,[],[f97,f51])).
% 1.83/0.61  fof(f97,plain,(
% 1.83/0.61    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | ~r1_tarski(X2,k2_relat_1(k6_relat_1(X1))) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2) )),
% 1.83/0.61    inference(resolution,[],[f47,f52])).
% 1.83/0.61  fof(f36,plain,(
% 1.83/0.61    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.83/0.61    inference(cnf_transformation,[],[f23])).
% 1.83/0.61  % (12985)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.83/0.61  fof(f371,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 1.83/0.61    inference(backward_demodulation,[],[f120,f362])).
% 1.83/0.61  fof(f362,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X1),X0)) )),
% 1.83/0.61    inference(superposition,[],[f112,f81])).
% 1.83/0.61  fof(f112,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2))) )),
% 1.83/0.61    inference(forward_demodulation,[],[f111,f87])).
% 1.83/0.61  fof(f87,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2))) )),
% 1.83/0.61    inference(unit_resulting_resolution,[],[f51,f43])).
% 1.83/0.61  fof(f111,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) )),
% 1.83/0.61    inference(forward_demodulation,[],[f108,f85])).
% 1.83/0.61  fof(f85,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.83/0.61    inference(unit_resulting_resolution,[],[f51,f44])).
% 1.83/0.61  fof(f44,plain,(
% 1.83/0.61    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f25])).
% 1.83/0.61  fof(f25,plain,(
% 1.83/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.83/0.61    inference(ennf_transformation,[],[f14])).
% 1.83/0.61  fof(f14,axiom,(
% 1.83/0.61    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.83/0.61  fof(f108,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2))) )),
% 1.83/0.61    inference(unit_resulting_resolution,[],[f51,f51,f53])).
% 1.83/0.61  fof(f53,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 1.83/0.61    inference(cnf_transformation,[],[f35])).
% 1.83/0.61  fof(f35,plain,(
% 1.83/0.61    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.83/0.61    inference(ennf_transformation,[],[f12])).
% 1.83/0.61  fof(f12,axiom,(
% 1.83/0.61    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 1.83/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
% 1.83/0.61  % SZS output end Proof for theBenchmark
% 1.83/0.61  % (12981)------------------------------
% 1.83/0.61  % (12981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.61  % (12981)Termination reason: Refutation
% 1.83/0.61  
% 1.83/0.61  % (12981)Memory used [KB]: 2046
% 1.83/0.61  % (12981)Time elapsed: 0.193 s
% 1.83/0.61  % (12981)------------------------------
% 1.83/0.61  % (12981)------------------------------
% 1.83/0.61  % (12966)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.83/0.61  % (12953)Success in time 0.251 s
%------------------------------------------------------------------------------
