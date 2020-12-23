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
% DateTime   : Thu Dec  3 12:53:53 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 134 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 345 expanded)
%              Number of equality atoms :   49 (  66 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f393,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f37,f367,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f367,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f360,f72])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f70,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f54,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f46,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f360,plain,(
    k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f46,f185])).

fof(f185,plain,(
    sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f180,f90])).

fof(f90,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f83,f36])).

fof(f36,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k1_relat_1(k7_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f180,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f124,f128])).

fof(f128,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f126,f100])).

fof(f100,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0) ),
    inference(resolution,[],[f88,f58])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k9_relat_1(k7_relat_1(sK1,X1),X0) = k9_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f126,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f68,f90])).

fof(f68,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f41,f60])).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f48,f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f124,plain,(
    ! [X1] : k3_xboole_0(X1,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X1)))) = k1_relat_1(k7_relat_1(sK1,X1)) ),
    inference(superposition,[],[f66,f85])).

fof(f85,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f40,f60])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f37,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (32626)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.50  % (32619)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.50  % (32626)Refutation not found, incomplete strategy% (32626)------------------------------
% 0.22/0.50  % (32626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32626)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (32626)Memory used [KB]: 10618
% 0.22/0.51  % (32626)Time elapsed: 0.079 s
% 0.22/0.51  % (32626)------------------------------
% 0.22/0.51  % (32626)------------------------------
% 0.22/0.51  % (32617)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (32610)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (32611)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (32614)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (32627)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (32613)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (32620)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.36/0.53  % (32630)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.36/0.53  % (32615)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.36/0.54  % (32620)Refutation not found, incomplete strategy% (32620)------------------------------
% 1.36/0.54  % (32620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (32636)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (32638)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.36/0.54  % (32627)Refutation not found, incomplete strategy% (32627)------------------------------
% 1.36/0.54  % (32627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (32627)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (32627)Memory used [KB]: 1918
% 1.36/0.54  % (32627)Time elapsed: 0.133 s
% 1.36/0.54  % (32627)------------------------------
% 1.36/0.54  % (32627)------------------------------
% 1.36/0.54  % (32628)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.54  % (32635)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.36/0.54  % (32620)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (32620)Memory used [KB]: 10746
% 1.36/0.54  % (32620)Time elapsed: 0.128 s
% 1.36/0.54  % (32620)------------------------------
% 1.36/0.54  % (32620)------------------------------
% 1.36/0.54  % (32628)Refutation not found, incomplete strategy% (32628)------------------------------
% 1.36/0.54  % (32628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (32628)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (32628)Memory used [KB]: 1663
% 1.36/0.54  % (32628)Time elapsed: 0.138 s
% 1.36/0.54  % (32628)------------------------------
% 1.36/0.54  % (32628)------------------------------
% 1.36/0.54  % (32617)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f393,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f37,f367,f53])).
% 1.36/0.54  fof(f53,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f34,plain,(
% 1.36/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.36/0.54    inference(nnf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.36/0.54  fof(f367,plain,(
% 1.36/0.54    k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.36/0.54    inference(forward_demodulation,[],[f360,f72])).
% 1.36/0.54  fof(f72,plain,(
% 1.36/0.54    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.36/0.54    inference(forward_demodulation,[],[f70,f64])).
% 1.36/0.54  fof(f64,plain,(
% 1.36/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.36/0.54    inference(resolution,[],[f54,f58])).
% 1.36/0.54  fof(f58,plain,(
% 1.36/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.54    inference(equality_resolution,[],[f51])).
% 1.36/0.54  fof(f51,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.36/0.54    inference(cnf_transformation,[],[f33])).
% 1.36/0.54  fof(f33,plain,(
% 1.36/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.54    inference(flattening,[],[f32])).
% 1.36/0.54  fof(f32,plain,(
% 1.36/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.54    inference(nnf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.54  fof(f54,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f70,plain,(
% 1.36/0.54    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 1.36/0.54    inference(superposition,[],[f46,f43])).
% 1.36/0.54  fof(f43,plain,(
% 1.36/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f20])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.36/0.54    inference(rectify,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.36/0.54  fof(f360,plain,(
% 1.36/0.54    k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.36/0.54    inference(superposition,[],[f46,f185])).
% 1.36/0.54  fof(f185,plain,(
% 1.36/0.54    sK0 = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.36/0.54    inference(forward_demodulation,[],[f180,f90])).
% 1.36/0.54  fof(f90,plain,(
% 1.36/0.54    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.36/0.54    inference(resolution,[],[f83,f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f30])).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.36/0.54    inference(flattening,[],[f21])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f19])).
% 1.36/0.54  fof(f19,negated_conjecture,(
% 1.36/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.36/0.54    inference(negated_conjecture,[],[f18])).
% 1.36/0.54  fof(f18,conjecture,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.36/0.54  fof(f83,plain,(
% 1.36/0.54    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) )),
% 1.36/0.54    inference(resolution,[],[f49,f35])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    v1_relat_1(sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f49,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f28])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.36/0.54    inference(flattening,[],[f27])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f16])).
% 1.36/0.54  fof(f16,axiom,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.36/0.54  fof(f180,plain,(
% 1.36/0.54    k1_relat_1(k7_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.36/0.54    inference(superposition,[],[f124,f128])).
% 1.36/0.54  fof(f128,plain,(
% 1.36/0.54    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 1.36/0.54    inference(forward_demodulation,[],[f126,f100])).
% 1.36/0.54  fof(f100,plain,(
% 1.36/0.54    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)) )),
% 1.36/0.54    inference(resolution,[],[f88,f58])).
% 1.36/0.54  fof(f88,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k7_relat_1(sK1,X1),X0) = k9_relat_1(sK1,X0)) )),
% 1.36/0.54    inference(resolution,[],[f42,f35])).
% 1.36/0.54  fof(f42,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f25])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,axiom,(
% 1.36/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 1.36/0.54  fof(f126,plain,(
% 1.36/0.54    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 1.36/0.54    inference(superposition,[],[f68,f90])).
% 1.36/0.54  fof(f68,plain,(
% 1.36/0.54    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.36/0.54    inference(resolution,[],[f41,f60])).
% 1.36/0.54  fof(f60,plain,(
% 1.36/0.54    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.36/0.54    inference(resolution,[],[f48,f35])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f26])).
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f12])).
% 1.36/0.54  fof(f12,axiom,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.36/0.54  fof(f41,plain,(
% 1.36/0.54    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f24])).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f13])).
% 1.36/0.54  fof(f13,axiom,(
% 1.36/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.36/0.54  fof(f124,plain,(
% 1.36/0.54    ( ! [X1] : (k3_xboole_0(X1,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X1)))) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 1.36/0.54    inference(superposition,[],[f66,f85])).
% 1.36/0.54  fof(f85,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 1.36/0.54    inference(resolution,[],[f56,f35])).
% 1.36/0.54  fof(f56,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f29])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.36/0.54    inference(ennf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.36/0.54  fof(f66,plain,(
% 1.36/0.54    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.36/0.54    inference(resolution,[],[f40,f60])).
% 1.36/0.54  fof(f40,plain,(
% 1.36/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f23])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,axiom,(
% 1.36/0.54    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (32617)------------------------------
% 1.36/0.54  % (32617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (32617)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (32617)Memory used [KB]: 2046
% 1.36/0.54  % (32617)Time elapsed: 0.129 s
% 1.36/0.54  % (32617)------------------------------
% 1.36/0.54  % (32617)------------------------------
% 1.36/0.54  % (32638)Refutation not found, incomplete strategy% (32638)------------------------------
% 1.36/0.54  % (32638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (32638)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (32638)Memory used [KB]: 10746
% 1.36/0.54  % (32638)Time elapsed: 0.117 s
% 1.36/0.54  % (32638)------------------------------
% 1.36/0.54  % (32638)------------------------------
% 1.36/0.54  % (32629)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.36/0.54  % (32609)Success in time 0.184 s
%------------------------------------------------------------------------------
