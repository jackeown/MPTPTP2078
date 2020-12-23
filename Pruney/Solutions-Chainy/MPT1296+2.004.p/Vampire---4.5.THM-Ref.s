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
% DateTime   : Thu Dec  3 13:13:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  56 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 122 expanded)
%              Number of equality atoms :   40 (  64 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(subsumption_resolution,[],[f69,f19])).

fof(f19,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

% (1239)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

fof(f69,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f68,f46])).

fof(f46,plain,(
    k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) = k4_xboole_0(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f21,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f43,plain,(
    r1_tarski(k6_setfam_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f42,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
      | r1_tarski(k6_setfam_1(X3,X2),X3) ) ),
    inference(resolution,[],[f22,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

fof(f68,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k4_xboole_0(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f65,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k4_xboole_0(sK0,k6_setfam_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f64,f17])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k4_xboole_0(X0,k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f32,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f57,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X2,X1)
      | k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f29,f27])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k6_setfam_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f23,f20])).

fof(f20,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:57:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (1245)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.48  % (1245)Refutation not found, incomplete strategy% (1245)------------------------------
% 0.19/0.48  % (1245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (1245)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (1245)Memory used [KB]: 10618
% 0.19/0.48  % (1245)Time elapsed: 0.099 s
% 0.19/0.48  % (1245)------------------------------
% 0.19/0.48  % (1245)------------------------------
% 0.19/0.50  % (1258)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.51  % (1252)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (1258)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(subsumption_resolution,[],[f69,f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,plain,(
% 0.19/0.51    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.51    inference(flattening,[],[f10])).
% 0.19/0.51  fof(f10,plain,(
% 0.19/0.51    ? [X0,X1] : ((k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.51    inference(ennf_transformation,[],[f9])).
% 0.19/0.51  % (1239)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.51  fof(f9,negated_conjecture,(
% 0.19/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 0.19/0.51    inference(negated_conjecture,[],[f8])).
% 0.19/0.51  fof(f8,conjecture,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 0.19/0.51    inference(forward_demodulation,[],[f68,f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) = k4_xboole_0(sK0,k6_setfam_1(sK0,sK1))),
% 0.19/0.51    inference(resolution,[],[f43,f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.19/0.51    inference(resolution,[],[f21,f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,plain,(
% 0.19/0.51    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    r1_tarski(k6_setfam_1(sK0,sK1),sK0)),
% 0.19/0.51    inference(resolution,[],[f42,f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) | r1_tarski(k6_setfam_1(X3,X2),X3)) )),
% 0.19/0.51    inference(resolution,[],[f22,f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k4_xboole_0(sK0,k6_setfam_1(sK0,sK1))),
% 0.19/0.51    inference(subsumption_resolution,[],[f65,f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    k1_xboole_0 != sK1),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k4_xboole_0(sK0,k6_setfam_1(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.19/0.51    inference(resolution,[],[f64,f17])).
% 0.19/0.51  fof(f64,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k4_xboole_0(X0,k6_setfam_1(X0,X1)) | k1_xboole_0 = X1) )),
% 0.19/0.51    inference(backward_demodulation,[],[f32,f59])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 0.19/0.51    inference(resolution,[],[f57,f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.51    inference(equality_resolution,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    ( ! [X2,X3,X1] : (~r1_tarski(X2,X1) | k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)) )),
% 0.19/0.51    inference(resolution,[],[f29,f27])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k6_setfam_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1) )),
% 0.19/0.51    inference(forward_demodulation,[],[f23,f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.51    inference(flattening,[],[f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ! [X0,X1] : ((k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.51    inference(ennf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (1258)------------------------------
% 0.19/0.51  % (1258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (1258)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (1258)Memory used [KB]: 1663
% 0.19/0.51  % (1258)Time elapsed: 0.120 s
% 0.19/0.51  % (1258)------------------------------
% 0.19/0.51  % (1258)------------------------------
% 0.19/0.51  % (1238)Success in time 0.161 s
%------------------------------------------------------------------------------
