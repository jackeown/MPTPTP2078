%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 123 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 245 expanded)
%              Number of equality atoms :   61 ( 130 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(subsumption_resolution,[],[f123,f73])).

fof(f73,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f61,f72])).

fof(f72,plain,(
    k4_xboole_0(sK0,k6_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f51,plain,(
    m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

fof(f61,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k4_xboole_0(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(resolution,[],[f40,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f31,f30])).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f41,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,sK0,k6_setfam_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f29,f30])).

fof(f29,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f123,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f120,f122])).

fof(f122,plain,(
    k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f121,f84])).

fof(f84,plain,(
    k6_setfam_1(sK0,sK1) = k4_xboole_0(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f83,f53])).

fof(f53,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f83,plain,(
    k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k4_xboole_0(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f74,f65])).

fof(f65,plain,(
    k1_xboole_0 != k7_setfam_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f64,f28])).

fof(f28,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k7_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f39,f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k7_setfam_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f74,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k4_xboole_0(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f57,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k4_xboole_0(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f43,f58])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k5_setfam_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f38,f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_setfam_1)).

fof(f57,plain,(
    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f37,f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f121,plain,(
    k4_xboole_0(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    inference(resolution,[],[f79,f32])).

fof(f79,plain,(
    m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f120,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))) ),
    inference(resolution,[],[f79,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:54:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (12639)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (12640)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (12639)Refutation not found, incomplete strategy% (12639)------------------------------
% 0.22/0.47  % (12639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (12639)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (12639)Memory used [KB]: 10618
% 0.22/0.47  % (12639)Time elapsed: 0.060 s
% 0.22/0.47  % (12639)------------------------------
% 0.22/0.47  % (12639)------------------------------
% 0.22/0.47  % (12640)Refutation not found, incomplete strategy% (12640)------------------------------
% 0.22/0.47  % (12640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12648)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (12653)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (12645)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (12653)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f123,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f61,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    k4_xboole_0(sK0,k6_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f51,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(resolution,[],[f35,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0,X1] : ((k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k4_xboole_0(sK0,k6_setfam_1(sK0,sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f41,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 0.22/0.48    inference(resolution,[],[f40,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f31,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,sK0,k6_setfam_1(sK0,sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f29,f30])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f120,f122])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))),
% 0.22/0.48    inference(forward_demodulation,[],[f121,f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    k6_setfam_1(sK0,sK1) = k4_xboole_0(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))),
% 0.22/0.48    inference(forward_demodulation,[],[f83,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f36,f27])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k4_xboole_0(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f74,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    k1_xboole_0 != k7_setfam_1(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f64,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    k1_xboole_0 != sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | k1_xboole_0 != k7_setfam_1(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f39,f27])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k7_setfam_1(X0,X1) != k1_xboole_0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : (k7_setfam_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(flattening,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1] : ((k7_setfam_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k7_setfam_1(X0,X1) = k1_xboole_0 & k1_xboole_0 != X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k4_xboole_0(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f57,f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k4_xboole_0(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1) )),
% 0.22/0.48    inference(backward_demodulation,[],[f43,f58])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k5_setfam_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1) )),
% 0.22/0.48    inference(forward_demodulation,[],[f38,f30])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : (k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : ((k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_setfam_1)).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.48    inference(resolution,[],[f37,f27])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    k4_xboole_0(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))),
% 0.22/0.48    inference(resolution,[],[f79,f32])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(resolution,[],[f57,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))))),
% 0.22/0.48    inference(resolution,[],[f79,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (12653)------------------------------
% 0.22/0.48  % (12653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12653)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (12653)Memory used [KB]: 1663
% 0.22/0.48  % (12653)Time elapsed: 0.065 s
% 0.22/0.48  % (12653)------------------------------
% 0.22/0.48  % (12653)------------------------------
% 0.22/0.48  % (12640)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  % (12633)Success in time 0.123 s
%------------------------------------------------------------------------------
