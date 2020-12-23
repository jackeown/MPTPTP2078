%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:27 EST 2020

% Result     : Theorem 3.62s
% Output     : Refutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 226 expanded)
%              Number of leaves         :   13 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  114 ( 360 expanded)
%              Number of equality atoms :   58 ( 158 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6662,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f6660])).

fof(f6660,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f37,f6143])).

fof(f6143,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f81,f6142])).

fof(f6142,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f6126,f125])).

fof(f125,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2)) ),
    inference(resolution,[],[f95,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f94,f81])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f92,f40])).

fof(f40,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f6126,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f1044,f1139])).

fof(f1139,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f1127,f91])).

fof(f91,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f89,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f89,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(resolution,[],[f51,f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f1127,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[],[f341,f261])).

fof(f261,plain,(
    ! [X4,X5] : k7_relat_1(k6_relat_1(X4),X5) = k3_xboole_0(k6_relat_1(X4),k7_relat_1(k6_relat_1(X4),X5)) ),
    inference(forward_demodulation,[],[f258,f39])).

fof(f258,plain,(
    ! [X4,X5] : k3_xboole_0(k6_relat_1(X4),k7_relat_1(k6_relat_1(X4),X5)) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X4),X5))) ),
    inference(superposition,[],[f91,f127])).

fof(f127,plain,(
    ! [X6,X5] : k6_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k6_relat_1(X5)),k7_relat_1(k6_relat_1(X5),X6)) ),
    inference(resolution,[],[f95,f83])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f70,f81])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1)) ),
    inference(resolution,[],[f53,f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f341,plain,(
    ! [X2,X3] : k3_xboole_0(k6_relat_1(X2),X3) = k7_relat_1(k3_xboole_0(k6_relat_1(X2),X3),k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3))) ),
    inference(superposition,[],[f76,f82])).

fof(f82,plain,(
    ! [X4,X2,X3] : k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X3),X4)) = k7_relat_1(k3_xboole_0(k6_relat_1(X3),X4),X2) ),
    inference(resolution,[],[f50,f62])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f49,f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f76,plain,(
    ! [X2,X1] : k3_xboole_0(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(k1_relat_1(k3_xboole_0(k6_relat_1(X1),X2))),k3_xboole_0(k6_relat_1(X1),X2)) ),
    inference(resolution,[],[f42,f62])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1044,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),k3_xboole_0(X6,X5)) = k7_relat_1(k6_relat_1(X7),k3_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f1031,f81])).

fof(f1031,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),k3_xboole_0(X6,X5)) = k5_relat_1(k6_relat_1(k3_xboole_0(X6,X5)),k6_relat_1(X7)) ),
    inference(superposition,[],[f728,f126])).

fof(f126,plain,(
    ! [X4,X3] : k6_relat_1(k3_xboole_0(X3,X4)) = k7_relat_1(k6_relat_1(X4),k3_xboole_0(X3,X4)) ),
    inference(resolution,[],[f95,f63])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f728,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(backward_demodulation,[],[f349,f701])).

fof(f701,plain,(
    ! [X14,X12,X13] : k5_relat_1(k6_relat_1(X14),k7_relat_1(k6_relat_1(X12),X13)) = k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X14) ),
    inference(superposition,[],[f82,f261])).

fof(f349,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f344,f81])).

fof(f344,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(resolution,[],[f140,f38])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f137,f81])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f101,f38])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f43,f38])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f81,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f50,f38])).

fof(f37,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f33])).

fof(f33,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (11631)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (11624)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (11639)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (11634)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (11634)Refutation not found, incomplete strategy% (11634)------------------------------
% 0.20/0.52  % (11634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11634)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11634)Memory used [KB]: 10618
% 0.20/0.52  % (11634)Time elapsed: 0.115 s
% 0.20/0.52  % (11634)------------------------------
% 0.20/0.52  % (11634)------------------------------
% 0.20/0.53  % (11637)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (11632)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (11630)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (11629)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (11626)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (11653)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (11653)Refutation not found, incomplete strategy% (11653)------------------------------
% 0.20/0.53  % (11653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11653)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11653)Memory used [KB]: 1663
% 0.20/0.53  % (11653)Time elapsed: 0.001 s
% 0.20/0.53  % (11653)------------------------------
% 0.20/0.53  % (11653)------------------------------
% 0.20/0.54  % (11648)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (11640)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (11645)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (11625)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (11640)Refutation not found, incomplete strategy% (11640)------------------------------
% 0.20/0.54  % (11640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11640)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11640)Memory used [KB]: 10618
% 0.20/0.54  % (11640)Time elapsed: 0.128 s
% 0.20/0.54  % (11640)------------------------------
% 0.20/0.54  % (11640)------------------------------
% 0.20/0.54  % (11627)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (11633)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (11648)Refutation not found, incomplete strategy% (11648)------------------------------
% 0.20/0.54  % (11648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11648)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11642)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (11648)Memory used [KB]: 10618
% 0.20/0.54  % (11648)Time elapsed: 0.125 s
% 0.20/0.54  % (11648)------------------------------
% 0.20/0.54  % (11648)------------------------------
% 0.20/0.54  % (11638)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (11638)Refutation not found, incomplete strategy% (11638)------------------------------
% 0.20/0.54  % (11638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11638)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11638)Memory used [KB]: 1663
% 0.20/0.54  % (11638)Time elapsed: 0.126 s
% 0.20/0.54  % (11638)------------------------------
% 0.20/0.54  % (11638)------------------------------
% 0.20/0.55  % (11650)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (11652)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (11642)Refutation not found, incomplete strategy% (11642)------------------------------
% 0.20/0.55  % (11642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11652)Refutation not found, incomplete strategy% (11652)------------------------------
% 0.20/0.55  % (11652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11652)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (11652)Memory used [KB]: 10618
% 0.20/0.55  % (11652)Time elapsed: 0.148 s
% 0.20/0.55  % (11652)------------------------------
% 0.20/0.55  % (11652)------------------------------
% 0.20/0.55  % (11647)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (11650)Refutation not found, incomplete strategy% (11650)------------------------------
% 0.20/0.55  % (11650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11628)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.55  % (11635)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (11635)Refutation not found, incomplete strategy% (11635)------------------------------
% 0.20/0.55  % (11635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11646)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (11641)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (11643)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.56  % (11641)Refutation not found, incomplete strategy% (11641)------------------------------
% 0.20/0.56  % (11641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (11641)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (11641)Memory used [KB]: 1663
% 0.20/0.56  % (11641)Time elapsed: 0.147 s
% 0.20/0.56  % (11641)------------------------------
% 0.20/0.56  % (11641)------------------------------
% 0.20/0.56  % (11635)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (11635)Memory used [KB]: 6140
% 0.20/0.56  % (11635)Time elapsed: 0.152 s
% 0.20/0.56  % (11635)------------------------------
% 0.20/0.56  % (11635)------------------------------
% 0.20/0.56  % (11642)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (11642)Memory used [KB]: 1663
% 0.20/0.56  % (11642)Time elapsed: 0.146 s
% 0.20/0.56  % (11642)------------------------------
% 0.20/0.56  % (11642)------------------------------
% 0.20/0.56  % (11625)Refutation not found, incomplete strategy% (11625)------------------------------
% 0.20/0.56  % (11625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (11625)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (11625)Memory used [KB]: 1663
% 0.20/0.56  % (11625)Time elapsed: 0.134 s
% 0.20/0.56  % (11625)------------------------------
% 0.20/0.56  % (11625)------------------------------
% 0.20/0.56  % (11650)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (11650)Memory used [KB]: 6140
% 0.20/0.56  % (11650)Time elapsed: 0.147 s
% 0.20/0.56  % (11650)------------------------------
% 0.20/0.56  % (11650)------------------------------
% 0.20/0.56  % (11644)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.56  % (11636)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (11636)Refutation not found, incomplete strategy% (11636)------------------------------
% 0.20/0.56  % (11636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (11651)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.58  % (11636)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (11636)Memory used [KB]: 10618
% 0.20/0.58  % (11636)Time elapsed: 0.162 s
% 0.20/0.58  % (11636)------------------------------
% 0.20/0.58  % (11636)------------------------------
% 0.20/0.58  % (11649)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.58  % (11651)Refutation not found, incomplete strategy% (11651)------------------------------
% 0.20/0.58  % (11651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (11651)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (11651)Memory used [KB]: 6140
% 0.20/0.58  % (11651)Time elapsed: 0.171 s
% 0.20/0.58  % (11651)------------------------------
% 0.20/0.58  % (11651)------------------------------
% 0.20/0.58  % (11649)Refutation not found, incomplete strategy% (11649)------------------------------
% 0.20/0.58  % (11649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (11649)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (11649)Memory used [KB]: 6140
% 0.20/0.58  % (11649)Time elapsed: 0.171 s
% 0.20/0.58  % (11649)------------------------------
% 0.20/0.58  % (11649)------------------------------
% 2.16/0.65  % (11639)Refutation not found, incomplete strategy% (11639)------------------------------
% 2.16/0.65  % (11639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.65  % (11660)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.16/0.66  % (11662)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.16/0.66  % (11639)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.66  
% 2.16/0.66  % (11639)Memory used [KB]: 6140
% 2.16/0.66  % (11639)Time elapsed: 0.220 s
% 2.16/0.66  % (11639)------------------------------
% 2.16/0.66  % (11639)------------------------------
% 2.16/0.66  % (11655)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.16/0.67  % (11660)Refutation not found, incomplete strategy% (11660)------------------------------
% 2.16/0.67  % (11660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.67  % (11656)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.16/0.67  % (11626)Refutation not found, incomplete strategy% (11626)------------------------------
% 2.16/0.67  % (11626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.67  % (11626)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.67  
% 2.16/0.67  % (11626)Memory used [KB]: 6140
% 2.16/0.67  % (11626)Time elapsed: 0.264 s
% 2.16/0.67  % (11626)------------------------------
% 2.16/0.67  % (11626)------------------------------
% 2.16/0.67  % (11660)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.67  
% 2.16/0.67  % (11660)Memory used [KB]: 10618
% 2.16/0.67  % (11660)Time elapsed: 0.090 s
% 2.16/0.67  % (11660)------------------------------
% 2.16/0.67  % (11660)------------------------------
% 2.16/0.68  % (11659)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.16/0.68  % (11627)Refutation not found, incomplete strategy% (11627)------------------------------
% 2.16/0.68  % (11627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.68  % (11627)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.68  
% 2.16/0.68  % (11627)Memory used [KB]: 6140
% 2.16/0.68  % (11627)Time elapsed: 0.276 s
% 2.16/0.68  % (11627)------------------------------
% 2.16/0.68  % (11627)------------------------------
% 2.16/0.68  % (11632)Refutation not found, incomplete strategy% (11632)------------------------------
% 2.16/0.68  % (11632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.69  % (11654)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.69  % (11632)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.69  
% 2.16/0.69  % (11632)Memory used [KB]: 6268
% 2.16/0.69  % (11632)Time elapsed: 0.253 s
% 2.16/0.69  % (11632)------------------------------
% 2.16/0.69  % (11632)------------------------------
% 2.16/0.69  % (11664)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.16/0.69  % (11661)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.16/0.70  % (11657)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.16/0.70  % (11658)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.16/0.70  % (11657)Refutation not found, incomplete strategy% (11657)------------------------------
% 2.16/0.70  % (11657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (11657)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (11657)Memory used [KB]: 10618
% 2.16/0.70  % (11657)Time elapsed: 0.119 s
% 2.16/0.70  % (11657)------------------------------
% 2.16/0.70  % (11657)------------------------------
% 2.16/0.70  % (11659)Refutation not found, incomplete strategy% (11659)------------------------------
% 2.16/0.70  % (11659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (11659)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (11659)Memory used [KB]: 1663
% 2.16/0.70  % (11659)Time elapsed: 0.122 s
% 2.16/0.70  % (11659)------------------------------
% 2.16/0.70  % (11659)------------------------------
% 2.16/0.70  % (11663)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.16/0.71  % (11663)Refutation not found, incomplete strategy% (11663)------------------------------
% 2.16/0.71  % (11663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.71  % (11663)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.71  
% 2.16/0.71  % (11663)Memory used [KB]: 10618
% 2.16/0.71  % (11663)Time elapsed: 0.126 s
% 2.16/0.71  % (11663)------------------------------
% 2.16/0.71  % (11663)------------------------------
% 2.16/0.71  % (11658)Refutation not found, incomplete strategy% (11658)------------------------------
% 2.16/0.71  % (11658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.71  % (11658)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.71  
% 2.16/0.71  % (11658)Memory used [KB]: 10618
% 2.16/0.71  % (11658)Time elapsed: 0.137 s
% 2.16/0.71  % (11658)------------------------------
% 2.16/0.71  % (11658)------------------------------
% 2.82/0.73  % (11665)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.82/0.73  % (11665)Refutation not found, incomplete strategy% (11665)------------------------------
% 2.82/0.73  % (11665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.73  % (11665)Termination reason: Refutation not found, incomplete strategy
% 2.82/0.73  
% 2.82/0.73  % (11665)Memory used [KB]: 10618
% 2.82/0.73  % (11665)Time elapsed: 0.128 s
% 2.82/0.73  % (11665)------------------------------
% 2.82/0.73  % (11665)------------------------------
% 2.82/0.77  % (11666)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.82/0.77  % (11672)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.82/0.79  % (11667)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.15/0.79  % (11667)Refutation not found, incomplete strategy% (11667)------------------------------
% 3.15/0.79  % (11667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.79  % (11667)Termination reason: Refutation not found, incomplete strategy
% 3.15/0.79  
% 3.15/0.79  % (11667)Memory used [KB]: 10618
% 3.15/0.79  % (11667)Time elapsed: 0.156 s
% 3.15/0.79  % (11667)------------------------------
% 3.15/0.79  % (11667)------------------------------
% 3.15/0.79  % (11668)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.15/0.80  % (11671)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.15/0.82  % (11669)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.15/0.83  % (11662)Refutation not found, incomplete strategy% (11662)------------------------------
% 3.15/0.83  % (11662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.83  % (11662)Termination reason: Refutation not found, incomplete strategy
% 3.15/0.83  
% 3.15/0.83  % (11662)Memory used [KB]: 6268
% 3.15/0.83  % (11662)Time elapsed: 0.242 s
% 3.15/0.83  % (11662)------------------------------
% 3.15/0.83  % (11662)------------------------------
% 3.15/0.83  % (11670)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.15/0.83  % (11674)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.15/0.84  % (11673)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.15/0.84  % (11673)Refutation not found, incomplete strategy% (11673)------------------------------
% 3.15/0.84  % (11673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.84  % (11673)Termination reason: Refutation not found, incomplete strategy
% 3.15/0.84  
% 3.15/0.84  % (11673)Memory used [KB]: 1663
% 3.15/0.84  % (11673)Time elapsed: 0.118 s
% 3.15/0.84  % (11673)------------------------------
% 3.15/0.84  % (11673)------------------------------
% 3.62/0.88  % (11668)Refutation not found, incomplete strategy% (11668)------------------------------
% 3.62/0.88  % (11668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.89  % (11668)Termination reason: Refutation not found, incomplete strategy
% 3.62/0.89  
% 3.62/0.89  % (11668)Memory used [KB]: 6140
% 3.62/0.89  % (11668)Time elapsed: 0.181 s
% 3.62/0.89  % (11668)------------------------------
% 3.62/0.89  % (11668)------------------------------
% 3.62/0.90  % (11631)Refutation found. Thanks to Tanya!
% 3.62/0.90  % SZS status Theorem for theBenchmark
% 3.62/0.90  % SZS output start Proof for theBenchmark
% 3.62/0.90  fof(f6662,plain,(
% 3.62/0.90    $false),
% 3.62/0.90    inference(trivial_inequality_removal,[],[f6660])).
% 3.62/0.90  fof(f6660,plain,(
% 3.62/0.90    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.62/0.90    inference(superposition,[],[f37,f6143])).
% 3.62/0.90  fof(f6143,plain,(
% 3.62/0.90    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0))) )),
% 3.62/0.90    inference(backward_demodulation,[],[f81,f6142])).
% 3.62/0.90  fof(f6142,plain,(
% 3.62/0.90    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 3.62/0.90    inference(forward_demodulation,[],[f6126,f125])).
% 3.62/0.90  fof(f125,plain,(
% 3.62/0.90    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2))) )),
% 3.62/0.90    inference(resolution,[],[f95,f44])).
% 3.62/0.90  fof(f44,plain,(
% 3.62/0.90    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.62/0.90    inference(cnf_transformation,[],[f3])).
% 3.62/0.90  fof(f3,axiom,(
% 3.62/0.90    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.62/0.90  fof(f95,plain,(
% 3.62/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.62/0.90    inference(forward_demodulation,[],[f94,f81])).
% 3.62/0.90  fof(f94,plain,(
% 3.62/0.90    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 3.62/0.90    inference(forward_demodulation,[],[f92,f40])).
% 3.62/0.90  fof(f40,plain,(
% 3.62/0.90    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.62/0.90    inference(cnf_transformation,[],[f11])).
% 3.62/0.90  fof(f11,axiom,(
% 3.62/0.90    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 3.62/0.90  fof(f92,plain,(
% 3.62/0.90    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 3.62/0.90    inference(resolution,[],[f54,f38])).
% 3.62/0.90  fof(f38,plain,(
% 3.62/0.90    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.62/0.90    inference(cnf_transformation,[],[f8])).
% 3.62/0.90  fof(f8,axiom,(
% 3.62/0.90    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 3.62/0.90  fof(f54,plain,(
% 3.62/0.90    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 3.62/0.90    inference(cnf_transformation,[],[f30])).
% 3.62/0.90  fof(f30,plain,(
% 3.62/0.90    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.62/0.90    inference(flattening,[],[f29])).
% 3.62/0.90  fof(f29,plain,(
% 3.62/0.90    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.62/0.90    inference(ennf_transformation,[],[f15])).
% 3.62/0.90  fof(f15,axiom,(
% 3.62/0.90    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 3.62/0.90  fof(f6126,plain,(
% 3.62/0.90    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 3.62/0.90    inference(superposition,[],[f1044,f1139])).
% 3.62/0.90  fof(f1139,plain,(
% 3.62/0.90    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k3_xboole_0(X0,X1))) )),
% 3.62/0.90    inference(forward_demodulation,[],[f1127,f91])).
% 3.62/0.90  fof(f91,plain,(
% 3.62/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 3.62/0.90    inference(forward_demodulation,[],[f89,f39])).
% 3.62/0.90  fof(f39,plain,(
% 3.62/0.90    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.62/0.90    inference(cnf_transformation,[],[f11])).
% 3.62/0.90  fof(f89,plain,(
% 3.62/0.90    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 3.62/0.90    inference(resolution,[],[f51,f38])).
% 3.62/0.90  fof(f51,plain,(
% 3.62/0.90    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 3.62/0.90    inference(cnf_transformation,[],[f27])).
% 3.62/0.90  fof(f27,plain,(
% 3.62/0.90    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.62/0.90    inference(ennf_transformation,[],[f17])).
% 3.62/0.90  fof(f17,axiom,(
% 3.62/0.90    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 3.62/0.90  fof(f1127,plain,(
% 3.62/0.90    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 3.62/0.90    inference(superposition,[],[f341,f261])).
% 3.62/0.90  fof(f261,plain,(
% 3.62/0.90    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X4),X5) = k3_xboole_0(k6_relat_1(X4),k7_relat_1(k6_relat_1(X4),X5))) )),
% 3.62/0.90    inference(forward_demodulation,[],[f258,f39])).
% 3.62/0.90  fof(f258,plain,(
% 3.62/0.90    ( ! [X4,X5] : (k3_xboole_0(k6_relat_1(X4),k7_relat_1(k6_relat_1(X4),X5)) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X4),X5)))) )),
% 3.62/0.90    inference(superposition,[],[f91,f127])).
% 3.62/0.90  fof(f127,plain,(
% 3.62/0.90    ( ! [X6,X5] : (k6_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k6_relat_1(X5)),k7_relat_1(k6_relat_1(X5),X6))) )),
% 3.62/0.90    inference(resolution,[],[f95,f83])).
% 3.62/0.90  fof(f83,plain,(
% 3.62/0.90    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X1))) )),
% 3.62/0.90    inference(backward_demodulation,[],[f70,f81])).
% 3.62/0.90  fof(f70,plain,(
% 3.62/0.90    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1))) )),
% 3.62/0.90    inference(resolution,[],[f53,f38])).
% 3.62/0.90  fof(f53,plain,(
% 3.62/0.90    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)) )),
% 3.62/0.90    inference(cnf_transformation,[],[f28])).
% 3.62/0.90  fof(f28,plain,(
% 3.62/0.90    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.62/0.90    inference(ennf_transformation,[],[f12])).
% 3.62/0.90  fof(f12,axiom,(
% 3.62/0.90    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 3.62/0.90  fof(f341,plain,(
% 3.62/0.90    ( ! [X2,X3] : (k3_xboole_0(k6_relat_1(X2),X3) = k7_relat_1(k3_xboole_0(k6_relat_1(X2),X3),k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)))) )),
% 3.62/0.90    inference(superposition,[],[f76,f82])).
% 3.62/0.90  fof(f82,plain,(
% 3.62/0.90    ( ! [X4,X2,X3] : (k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X3),X4)) = k7_relat_1(k3_xboole_0(k6_relat_1(X3),X4),X2)) )),
% 3.62/0.90    inference(resolution,[],[f50,f62])).
% 3.62/0.90  fof(f62,plain,(
% 3.62/0.90    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) )),
% 3.62/0.90    inference(resolution,[],[f49,f38])).
% 3.62/0.90  fof(f49,plain,(
% 3.62/0.90    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 3.62/0.90    inference(cnf_transformation,[],[f25])).
% 3.62/0.90  fof(f25,plain,(
% 3.62/0.90    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 3.62/0.90    inference(ennf_transformation,[],[f9])).
% 3.62/0.90  fof(f9,axiom,(
% 3.62/0.90    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 3.62/0.90  fof(f50,plain,(
% 3.62/0.90    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 3.62/0.90    inference(cnf_transformation,[],[f26])).
% 3.62/0.90  fof(f26,plain,(
% 3.62/0.90    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.62/0.90    inference(ennf_transformation,[],[f18])).
% 3.62/0.90  fof(f18,axiom,(
% 3.62/0.90    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 3.62/0.90  fof(f76,plain,(
% 3.62/0.90    ( ! [X2,X1] : (k3_xboole_0(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(k1_relat_1(k3_xboole_0(k6_relat_1(X1),X2))),k3_xboole_0(k6_relat_1(X1),X2))) )),
% 3.62/0.90    inference(resolution,[],[f42,f62])).
% 3.62/0.90  fof(f42,plain,(
% 3.62/0.90    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 3.62/0.90    inference(cnf_transformation,[],[f23])).
% 3.62/0.90  fof(f23,plain,(
% 3.62/0.90    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 3.62/0.90    inference(ennf_transformation,[],[f14])).
% 3.62/0.90  fof(f14,axiom,(
% 3.62/0.90    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 3.62/0.90  fof(f1044,plain,(
% 3.62/0.90    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),k3_xboole_0(X6,X5)) = k7_relat_1(k6_relat_1(X7),k3_xboole_0(X6,X5))) )),
% 3.62/0.90    inference(forward_demodulation,[],[f1031,f81])).
% 3.62/0.90  fof(f1031,plain,(
% 3.62/0.90    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),k3_xboole_0(X6,X5)) = k5_relat_1(k6_relat_1(k3_xboole_0(X6,X5)),k6_relat_1(X7))) )),
% 3.62/0.90    inference(superposition,[],[f728,f126])).
% 3.62/0.90  fof(f126,plain,(
% 3.62/0.90    ( ! [X4,X3] : (k6_relat_1(k3_xboole_0(X3,X4)) = k7_relat_1(k6_relat_1(X4),k3_xboole_0(X3,X4))) )),
% 3.62/0.90    inference(resolution,[],[f95,f63])).
% 3.62/0.90  fof(f63,plain,(
% 3.62/0.90    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 3.62/0.90    inference(superposition,[],[f44,f45])).
% 3.62/0.90  fof(f45,plain,(
% 3.62/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.62/0.90    inference(cnf_transformation,[],[f1])).
% 3.62/0.90  fof(f1,axiom,(
% 3.62/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.62/0.90  fof(f728,plain,(
% 3.62/0.90    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) )),
% 3.62/0.90    inference(backward_demodulation,[],[f349,f701])).
% 3.62/0.90  fof(f701,plain,(
% 3.62/0.90    ( ! [X14,X12,X13] : (k5_relat_1(k6_relat_1(X14),k7_relat_1(k6_relat_1(X12),X13)) = k7_relat_1(k7_relat_1(k6_relat_1(X12),X13),X14)) )),
% 3.62/0.90    inference(superposition,[],[f82,f261])).
% 3.62/0.90  fof(f349,plain,(
% 3.62/0.90    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 3.62/0.90    inference(forward_demodulation,[],[f344,f81])).
% 3.62/0.90  fof(f344,plain,(
% 3.62/0.90    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 3.62/0.90    inference(resolution,[],[f140,f38])).
% 3.62/0.90  fof(f140,plain,(
% 3.62/0.90    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 3.62/0.90    inference(forward_demodulation,[],[f137,f81])).
% 3.62/0.90  fof(f137,plain,(
% 3.62/0.90    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 3.62/0.90    inference(resolution,[],[f101,f38])).
% 3.62/0.90  fof(f101,plain,(
% 3.62/0.90    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 3.62/0.90    inference(resolution,[],[f43,f38])).
% 3.62/0.90  fof(f43,plain,(
% 3.62/0.90    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.62/0.90    inference(cnf_transformation,[],[f24])).
% 3.62/0.90  fof(f24,plain,(
% 3.62/0.90    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.62/0.90    inference(ennf_transformation,[],[f10])).
% 3.62/0.90  fof(f10,axiom,(
% 3.62/0.90    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 3.62/0.90  fof(f81,plain,(
% 3.62/0.90    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.62/0.90    inference(resolution,[],[f50,f38])).
% 3.62/0.90  fof(f37,plain,(
% 3.62/0.90    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.62/0.90    inference(cnf_transformation,[],[f34])).
% 3.62/0.90  fof(f34,plain,(
% 3.62/0.90    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.62/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f33])).
% 3.62/0.90  fof(f33,plain,(
% 3.62/0.90    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.62/0.90    introduced(choice_axiom,[])).
% 3.62/0.90  fof(f21,plain,(
% 3.62/0.90    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.62/0.90    inference(ennf_transformation,[],[f20])).
% 3.62/0.90  fof(f20,negated_conjecture,(
% 3.62/0.90    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.62/0.90    inference(negated_conjecture,[],[f19])).
% 3.62/0.90  fof(f19,conjecture,(
% 3.62/0.90    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.62/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 3.62/0.90  % SZS output end Proof for theBenchmark
% 3.62/0.90  % (11631)------------------------------
% 3.62/0.90  % (11631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.90  % (11631)Termination reason: Refutation
% 3.62/0.90  
% 3.62/0.90  % (11631)Memory used [KB]: 7036
% 3.62/0.90  % (11631)Time elapsed: 0.475 s
% 3.62/0.90  % (11631)------------------------------
% 3.62/0.90  % (11631)------------------------------
% 3.92/0.91  % (11623)Success in time 0.561 s
%------------------------------------------------------------------------------
