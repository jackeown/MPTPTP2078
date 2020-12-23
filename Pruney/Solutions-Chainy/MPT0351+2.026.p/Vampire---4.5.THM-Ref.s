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
% DateTime   : Thu Dec  3 12:44:06 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 102 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 145 expanded)
%              Number of equality atoms :   42 (  88 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(global_subsumption,[],[f49,f192])).

fof(f192,plain,(
    sK0 = k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f159,f141])).

fof(f141,plain,(
    sK0 = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f67,f135])).

fof(f135,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f134,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f134,plain,(
    ! [X2,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X2)) = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f124,f111])).

fof(f111,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f107,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f107,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f45,f43])).

fof(f43,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f25,f42])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f124,plain,(
    ! [X2,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X2,k1_xboole_0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f105,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f105,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f29,f29])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f67,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f61,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f61,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f22,f20,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f22,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f159,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f20,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f46,f45])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f26,f23])).

fof(f23,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f49,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f21,f23])).

fof(f21,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:05:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.20/0.56  % (1471)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.55/0.56  % (1473)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.55/0.56  % (1496)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.55/0.56  % (1471)Refutation not found, incomplete strategy% (1471)------------------------------
% 1.55/0.56  % (1471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (1498)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.55/0.57  % (1479)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.55/0.57  % (1471)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (1471)Memory used [KB]: 1663
% 1.55/0.57  % (1471)Time elapsed: 0.135 s
% 1.55/0.57  % (1471)------------------------------
% 1.55/0.57  % (1471)------------------------------
% 1.55/0.57  % (1479)Refutation not found, incomplete strategy% (1479)------------------------------
% 1.55/0.57  % (1479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (1479)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (1479)Memory used [KB]: 10618
% 1.55/0.57  % (1479)Time elapsed: 0.148 s
% 1.55/0.57  % (1479)------------------------------
% 1.55/0.57  % (1479)------------------------------
% 1.55/0.57  % (1481)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.55/0.58  % (1473)Refutation not found, incomplete strategy% (1473)------------------------------
% 1.55/0.58  % (1473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (1473)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (1473)Memory used [KB]: 10746
% 1.55/0.58  % (1473)Time elapsed: 0.143 s
% 1.55/0.58  % (1473)------------------------------
% 1.55/0.58  % (1473)------------------------------
% 1.55/0.58  % (1481)Refutation not found, incomplete strategy% (1481)------------------------------
% 1.55/0.58  % (1481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (1481)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (1481)Memory used [KB]: 10618
% 1.55/0.58  % (1481)Time elapsed: 0.154 s
% 1.55/0.58  % (1481)------------------------------
% 1.55/0.58  % (1481)------------------------------
% 1.55/0.59  % (1498)Refutation not found, incomplete strategy% (1498)------------------------------
% 1.55/0.59  % (1498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (1498)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (1498)Memory used [KB]: 10746
% 1.55/0.59  % (1498)Time elapsed: 0.149 s
% 1.55/0.59  % (1498)------------------------------
% 1.55/0.59  % (1498)------------------------------
% 1.55/0.59  % (1496)Refutation found. Thanks to Tanya!
% 1.55/0.59  % SZS status Theorem for theBenchmark
% 1.55/0.59  % SZS output start Proof for theBenchmark
% 1.55/0.59  fof(f193,plain,(
% 1.55/0.59    $false),
% 1.55/0.59    inference(global_subsumption,[],[f49,f192])).
% 1.55/0.59  fof(f192,plain,(
% 1.55/0.59    sK0 = k4_subset_1(sK0,sK1,sK0)),
% 1.55/0.59    inference(forward_demodulation,[],[f159,f141])).
% 1.55/0.59  fof(f141,plain,(
% 1.55/0.59    sK0 = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f67,f135])).
% 1.55/0.59  fof(f135,plain,(
% 1.55/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2 | ~r1_tarski(X1,X2)) )),
% 1.55/0.59    inference(forward_demodulation,[],[f134,f45])).
% 1.55/0.59  fof(f45,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.55/0.59    inference(definition_unfolding,[],[f30,f42])).
% 1.55/0.59  fof(f42,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.55/0.59    inference(definition_unfolding,[],[f28,f29])).
% 1.55/0.59  fof(f29,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f6])).
% 1.55/0.59  fof(f6,axiom,(
% 1.55/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.55/0.59  fof(f28,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f8])).
% 1.55/0.59  fof(f8,axiom,(
% 1.55/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.55/0.59  fof(f30,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f4])).
% 1.55/0.59  fof(f4,axiom,(
% 1.55/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.55/0.59  fof(f134,plain,(
% 1.55/0.59    ( ! [X2,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = X2 | ~r1_tarski(X1,X2)) )),
% 1.55/0.59    inference(forward_demodulation,[],[f124,f111])).
% 1.55/0.59  fof(f111,plain,(
% 1.55/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.59    inference(forward_demodulation,[],[f107,f24])).
% 1.55/0.59  fof(f24,plain,(
% 1.55/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f3])).
% 1.55/0.59  fof(f3,axiom,(
% 1.55/0.59    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.55/0.59  fof(f107,plain,(
% 1.55/0.59    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.55/0.59    inference(superposition,[],[f45,f43])).
% 1.55/0.59  fof(f43,plain,(
% 1.55/0.59    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 1.55/0.59    inference(definition_unfolding,[],[f25,f42])).
% 1.55/0.59  fof(f25,plain,(
% 1.55/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.59    inference(cnf_transformation,[],[f2])).
% 1.55/0.59  fof(f2,axiom,(
% 1.55/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.55/0.59  fof(f124,plain,(
% 1.55/0.59    ( ! [X2,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2)) )),
% 1.55/0.59    inference(superposition,[],[f105,f39])).
% 1.55/0.59  fof(f39,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f1])).
% 1.55/0.59  fof(f1,axiom,(
% 1.55/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.55/0.59  fof(f105,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X1,X1,X0))) )),
% 1.55/0.59    inference(superposition,[],[f45,f44])).
% 1.55/0.59  fof(f44,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.55/0.59    inference(definition_unfolding,[],[f27,f29,f29])).
% 1.55/0.59  fof(f27,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f5])).
% 1.55/0.59  fof(f5,axiom,(
% 1.55/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.55/0.59  fof(f67,plain,(
% 1.55/0.59    r1_tarski(sK1,sK0)),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f61,f47])).
% 1.55/0.59  fof(f47,plain,(
% 1.55/0.59    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.55/0.59    inference(equality_resolution,[],[f36])).
% 1.55/0.59  fof(f36,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.55/0.59    inference(cnf_transformation,[],[f7])).
% 1.55/0.59  fof(f7,axiom,(
% 1.55/0.59    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.55/0.59  fof(f61,plain,(
% 1.55/0.59    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f22,f20,f34])).
% 1.55/0.59  fof(f34,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f17])).
% 1.55/0.59  fof(f17,plain,(
% 1.55/0.59    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f9])).
% 1.55/0.59  fof(f9,axiom,(
% 1.55/0.59    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.55/0.59  fof(f20,plain,(
% 1.55/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.55/0.59    inference(cnf_transformation,[],[f16])).
% 1.55/0.59  fof(f16,plain,(
% 1.55/0.59    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f15])).
% 1.55/0.59  fof(f15,negated_conjecture,(
% 1.55/0.59    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.55/0.59    inference(negated_conjecture,[],[f14])).
% 1.55/0.59  fof(f14,conjecture,(
% 1.55/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 1.55/0.59  fof(f22,plain,(
% 1.55/0.59    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f12])).
% 1.55/0.59  fof(f12,axiom,(
% 1.55/0.59    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.55/0.59  fof(f159,plain,(
% 1.55/0.59    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.55/0.59    inference(unit_resulting_resolution,[],[f50,f20,f51])).
% 1.55/0.59  fof(f51,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.55/0.59    inference(forward_demodulation,[],[f46,f45])).
% 1.55/0.59  fof(f46,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 1.55/0.59    inference(definition_unfolding,[],[f41,f42])).
% 1.55/0.59  fof(f41,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f19])).
% 1.55/0.59  fof(f19,plain,(
% 1.55/0.59    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.59    inference(flattening,[],[f18])).
% 1.55/0.59  fof(f18,plain,(
% 1.55/0.59    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.55/0.59    inference(ennf_transformation,[],[f13])).
% 1.55/0.59  fof(f13,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.55/0.59  fof(f50,plain,(
% 1.55/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.55/0.59    inference(forward_demodulation,[],[f26,f23])).
% 1.55/0.59  fof(f23,plain,(
% 1.55/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.55/0.59    inference(cnf_transformation,[],[f10])).
% 1.55/0.59  fof(f10,axiom,(
% 1.55/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.55/0.59  fof(f26,plain,(
% 1.55/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f11])).
% 1.55/0.59  fof(f11,axiom,(
% 1.55/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.55/0.59  fof(f49,plain,(
% 1.55/0.59    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 1.55/0.59    inference(backward_demodulation,[],[f21,f23])).
% 1.55/0.59  fof(f21,plain,(
% 1.55/0.59    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.55/0.59    inference(cnf_transformation,[],[f16])).
% 1.55/0.59  % SZS output end Proof for theBenchmark
% 1.55/0.59  % (1496)------------------------------
% 1.55/0.59  % (1496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (1496)Termination reason: Refutation
% 1.55/0.59  
% 1.55/0.59  % (1496)Memory used [KB]: 6268
% 1.55/0.59  % (1496)Time elapsed: 0.150 s
% 1.55/0.59  % (1496)------------------------------
% 1.55/0.59  % (1496)------------------------------
% 1.55/0.59  % (1470)Success in time 0.223 s
%------------------------------------------------------------------------------
