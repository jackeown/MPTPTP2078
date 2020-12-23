%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 179 expanded)
%              Number of leaves         :    6 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :   61 ( 359 expanded)
%              Number of equality atoms :   46 ( 224 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1172,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1171,f15])).

fof(f15,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1171,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f658,f1170])).

fof(f1170,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f1147,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f18,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f1147,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f814,f872])).

fof(f872,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f807,f16])).

fof(f807,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f12,f806])).

fof(f806,plain,(
    sK0 = sK3 ),
    inference(backward_demodulation,[],[f762,f805])).

fof(f805,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK3)) ),
    inference(forward_demodulation,[],[f781,f18])).

fof(f781,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK3)) = k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f66,f12])).

fof(f66,plain,(
    ! [X12] : k3_xboole_0(sK0,k2_xboole_0(sK2,X12)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X12)) ),
    inference(superposition,[],[f26,f24])).

fof(f24,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f19,f13])).

fof(f13,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2)) ),
    inference(superposition,[],[f20,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f762,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK3)) ),
    inference(forward_demodulation,[],[f740,f17])).

fof(f740,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK3,sK0)) ),
    inference(superposition,[],[f51,f55])).

fof(f55,plain,(
    sK3 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f22,f12])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(sK3,k2_xboole_0(X0,sK1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK3,X0)) ),
    inference(forward_demodulation,[],[f47,f16])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(sK3,k2_xboole_0(X0,sK1)) = k2_xboole_0(k3_xboole_0(sK3,X0),k1_xboole_0) ),
    inference(superposition,[],[f20,f25])).

fof(f25,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f19,f14])).

fof(f14,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f814,plain,(
    ! [X14] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X14)) = k3_xboole_0(sK1,k2_xboole_0(sK0,X14)) ),
    inference(backward_demodulation,[],[f68,f806])).

fof(f68,plain,(
    ! [X14] : k3_xboole_0(sK1,k2_xboole_0(sK3,X14)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X14)) ),
    inference(superposition,[],[f26,f25])).

fof(f658,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f632,f17])).

fof(f632,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f41,f21])).

fof(f21,plain,(
    sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f18,f12])).

fof(f41,plain,(
    ! [X1] : k3_xboole_0(sK2,k2_xboole_0(sK0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,X1)) ),
    inference(superposition,[],[f20,f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:14:56 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.48  % (15793)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (15802)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (15797)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (15806)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (15799)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (15798)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (15804)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (15805)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (15792)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (15794)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (15795)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (15790)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (15788)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (15789)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (15808)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (15808)Refutation not found, incomplete strategy% (15808)------------------------------
% 0.22/0.52  % (15808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15808)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15808)Memory used [KB]: 10490
% 0.22/0.52  % (15808)Time elapsed: 0.105 s
% 0.22/0.52  % (15808)------------------------------
% 0.22/0.52  % (15808)------------------------------
% 0.22/0.52  % (15791)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (15796)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (15801)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.53  % (15800)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (15807)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.54  % (15803)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.54  % (15800)Refutation not found, incomplete strategy% (15800)------------------------------
% 0.22/0.54  % (15800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15800)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15800)Memory used [KB]: 6012
% 0.22/0.54  % (15800)Time elapsed: 0.003 s
% 0.22/0.54  % (15800)------------------------------
% 0.22/0.54  % (15800)------------------------------
% 0.22/0.59  % (15805)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f1172,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(subsumption_resolution,[],[f1171,f15])).
% 0.22/0.59  fof(f15,plain,(
% 0.22/0.59    sK1 != sK2),
% 0.22/0.59    inference(cnf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,plain,(
% 0.22/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 0.22/0.59    inference(flattening,[],[f9])).
% 0.22/0.59  fof(f9,plain,(
% 0.22/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.22/0.59    inference(negated_conjecture,[],[f6])).
% 0.22/0.59  fof(f6,conjecture,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 0.22/0.59  fof(f1171,plain,(
% 0.22/0.59    sK1 = sK2),
% 0.22/0.59    inference(backward_demodulation,[],[f658,f1170])).
% 0.22/0.59  fof(f1170,plain,(
% 0.22/0.59    sK1 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2))),
% 0.22/0.59    inference(forward_demodulation,[],[f1147,f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) )),
% 0.22/0.59    inference(superposition,[],[f18,f16])).
% 0.22/0.59  fof(f16,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.22/0.59  fof(f1147,plain,(
% 0.22/0.59    k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 0.22/0.59    inference(superposition,[],[f814,f872])).
% 0.22/0.59  fof(f872,plain,(
% 0.22/0.59    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)),
% 0.22/0.59    inference(superposition,[],[f807,f16])).
% 0.22/0.59  fof(f807,plain,(
% 0.22/0.59    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)),
% 0.22/0.59    inference(backward_demodulation,[],[f12,f806])).
% 0.22/0.59  fof(f806,plain,(
% 0.22/0.59    sK0 = sK3),
% 0.22/0.59    inference(backward_demodulation,[],[f762,f805])).
% 0.22/0.59  fof(f805,plain,(
% 0.22/0.59    sK0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK3))),
% 0.22/0.59    inference(forward_demodulation,[],[f781,f18])).
% 0.22/0.59  fof(f781,plain,(
% 0.22/0.59    k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK3)) = k3_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.22/0.59    inference(superposition,[],[f66,f12])).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    ( ! [X12] : (k3_xboole_0(sK0,k2_xboole_0(sK2,X12)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X12))) )),
% 0.22/0.59    inference(superposition,[],[f26,f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 0.22/0.59    inference(resolution,[],[f19,f13])).
% 0.22/0.59  fof(f13,plain,(
% 0.22/0.59    r1_xboole_0(sK2,sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f10])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,plain,(
% 0.22/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,plain,(
% 0.22/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.59    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) )),
% 0.22/0.59    inference(superposition,[],[f20,f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.22/0.59  fof(f762,plain,(
% 0.22/0.59    sK3 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK3))),
% 0.22/0.59    inference(forward_demodulation,[],[f740,f17])).
% 0.22/0.59  fof(f740,plain,(
% 0.22/0.59    sK3 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK3,sK0))),
% 0.22/0.59    inference(superposition,[],[f51,f55])).
% 0.22/0.59  fof(f55,plain,(
% 0.22/0.59    sK3 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.22/0.59    inference(superposition,[],[f22,f12])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ( ! [X0] : (k3_xboole_0(sK3,k2_xboole_0(X0,sK1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK3,X0))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f47,f16])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    ( ! [X0] : (k3_xboole_0(sK3,k2_xboole_0(X0,sK1)) = k2_xboole_0(k3_xboole_0(sK3,X0),k1_xboole_0)) )),
% 0.22/0.59    inference(superposition,[],[f20,f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 0.22/0.59    inference(resolution,[],[f19,f14])).
% 0.22/0.59  fof(f14,plain,(
% 0.22/0.59    r1_xboole_0(sK3,sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f10])).
% 0.22/0.59  fof(f12,plain,(
% 0.22/0.59    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.22/0.59    inference(cnf_transformation,[],[f10])).
% 0.22/0.59  fof(f814,plain,(
% 0.22/0.59    ( ! [X14] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X14)) = k3_xboole_0(sK1,k2_xboole_0(sK0,X14))) )),
% 0.22/0.59    inference(backward_demodulation,[],[f68,f806])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    ( ! [X14] : (k3_xboole_0(sK1,k2_xboole_0(sK3,X14)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X14))) )),
% 0.22/0.59    inference(superposition,[],[f26,f25])).
% 0.22/0.59  fof(f658,plain,(
% 0.22/0.59    sK2 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2))),
% 0.22/0.59    inference(forward_demodulation,[],[f632,f17])).
% 0.22/0.59  fof(f632,plain,(
% 0.22/0.59    sK2 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,sK1))),
% 0.22/0.59    inference(superposition,[],[f41,f21])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.22/0.59    inference(superposition,[],[f18,f12])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ( ! [X1] : (k3_xboole_0(sK2,k2_xboole_0(sK0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,X1))) )),
% 0.22/0.59    inference(superposition,[],[f20,f24])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (15805)------------------------------
% 0.22/0.59  % (15805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (15805)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (15805)Memory used [KB]: 2558
% 0.22/0.59  % (15805)Time elapsed: 0.177 s
% 0.22/0.59  % (15805)------------------------------
% 0.22/0.59  % (15805)------------------------------
% 0.22/0.60  % (15787)Success in time 0.226 s
%------------------------------------------------------------------------------
