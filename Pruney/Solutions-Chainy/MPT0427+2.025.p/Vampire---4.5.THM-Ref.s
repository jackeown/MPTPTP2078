%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 441 expanded)
%              Number of leaves         :    8 (  88 expanded)
%              Depth                    :   19
%              Number of atoms          :  119 (1286 expanded)
%              Number of equality atoms :   48 ( 329 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (9853)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (9868)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f123,plain,(
    $false ),
    inference(subsumption_resolution,[],[f122,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f122,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f121,f101])).

fof(f101,plain,(
    sK0 = k8_setfam_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f86,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f86,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f20,f83])).

fof(f83,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f82,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f82,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f36,f68])).

fof(f68,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f67,f35])).

fof(f35,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    inference(resolution,[],[f18,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f18,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f67,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f50])).

fof(f50,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f47,f45])).

fof(f45,plain,(
    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f20,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f47,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f20,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f19,f43])).

fof(f43,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f40,f38])).

fof(f38,plain,(
    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f17,f30])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f17,f22])).

fof(f19,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f18,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f121,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) ),
    inference(forward_demodulation,[],[f107,f108])).

fof(f108,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f106,f58])).

fof(f58,plain,(
    r1_tarski(k1_setfam_1(sK2),sK0) ),
    inference(resolution,[],[f42,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f42,plain,(
    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f39,f38])).

fof(f39,plain,(
    m1_subset_1(k6_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f17,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

fof(f106,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f93,f101])).

fof(f93,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f57,f83])).

fof(f107,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(backward_demodulation,[],[f85,f101])).

fof(f85,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f19,f83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:30:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (9854)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (9852)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (9859)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (9854)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 1.15/0.51  % (9853)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.15/0.51  % (9868)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.15/0.51  fof(f123,plain,(
% 1.15/0.51    $false),
% 1.15/0.51    inference(subsumption_resolution,[],[f122,f34])).
% 1.15/0.51  fof(f34,plain,(
% 1.15/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.15/0.51    inference(equality_resolution,[],[f25])).
% 1.15/0.51  fof(f25,plain,(
% 1.15/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.15/0.51    inference(cnf_transformation,[],[f1])).
% 1.15/0.51  fof(f1,axiom,(
% 1.15/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.15/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.15/0.51  fof(f122,plain,(
% 1.15/0.51    ~r1_tarski(sK0,sK0)),
% 1.15/0.51    inference(forward_demodulation,[],[f121,f101])).
% 1.15/0.51  fof(f101,plain,(
% 1.15/0.51    sK0 = k8_setfam_1(sK0,k1_xboole_0)),
% 1.15/0.51    inference(resolution,[],[f86,f32])).
% 1.15/0.51  fof(f32,plain,(
% 1.15/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.15/0.51    inference(equality_resolution,[],[f21])).
% 1.15/0.51  fof(f21,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 1.15/0.51    inference(cnf_transformation,[],[f12])).
% 1.15/0.51  fof(f12,plain,(
% 1.15/0.51    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.15/0.51    inference(ennf_transformation,[],[f3])).
% 1.15/0.51  fof(f3,axiom,(
% 1.15/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.15/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.15/0.51  fof(f86,plain,(
% 1.15/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.15/0.51    inference(backward_demodulation,[],[f20,f83])).
% 1.15/0.51  fof(f83,plain,(
% 1.15/0.51    k1_xboole_0 = sK1),
% 1.15/0.51    inference(subsumption_resolution,[],[f82,f28])).
% 1.15/0.51  fof(f28,plain,(
% 1.15/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f2])).
% 1.15/0.51  fof(f2,axiom,(
% 1.15/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.15/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.15/0.51  fof(f82,plain,(
% 1.15/0.51    ~r1_tarski(k1_xboole_0,sK1) | k1_xboole_0 = sK1),
% 1.15/0.51    inference(duplicate_literal_removal,[],[f72])).
% 1.15/0.51  fof(f72,plain,(
% 1.15/0.51    ~r1_tarski(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.15/0.51    inference(superposition,[],[f36,f68])).
% 1.15/0.51  fof(f68,plain,(
% 1.15/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.15/0.51    inference(subsumption_resolution,[],[f67,f35])).
% 1.15/0.51  fof(f35,plain,(
% 1.15/0.51    k1_xboole_0 = sK1 | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 1.15/0.51    inference(resolution,[],[f18,f31])).
% 1.15/0.51  fof(f31,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 1.15/0.51    inference(cnf_transformation,[],[f16])).
% 1.15/0.51  fof(f16,plain,(
% 1.15/0.51    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.15/0.51    inference(flattening,[],[f15])).
% 1.15/0.51  fof(f15,plain,(
% 1.15/0.51    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.15/0.51    inference(ennf_transformation,[],[f7])).
% 1.15/0.51  fof(f7,axiom,(
% 1.15/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.15/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.15/0.51  fof(f18,plain,(
% 1.15/0.51    r1_tarski(sK1,sK2)),
% 1.15/0.51    inference(cnf_transformation,[],[f11])).
% 1.15/0.51  fof(f11,plain,(
% 1.15/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.15/0.51    inference(flattening,[],[f10])).
% 1.15/0.51  fof(f10,plain,(
% 1.15/0.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.15/0.51    inference(ennf_transformation,[],[f9])).
% 1.15/0.51  fof(f9,negated_conjecture,(
% 1.15/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.15/0.51    inference(negated_conjecture,[],[f8])).
% 1.15/0.51  fof(f8,conjecture,(
% 1.15/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.15/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 1.15/0.51  fof(f67,plain,(
% 1.15/0.51    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.15/0.51    inference(superposition,[],[f57,f50])).
% 1.15/0.51  fof(f50,plain,(
% 1.15/0.51    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1),
% 1.15/0.51    inference(forward_demodulation,[],[f47,f45])).
% 1.15/0.51  fof(f45,plain,(
% 1.15/0.51    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)),
% 1.15/0.51    inference(resolution,[],[f20,f30])).
% 1.15/0.51  fof(f30,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f14])).
% 1.15/0.51  fof(f14,plain,(
% 1.15/0.51    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.15/0.51    inference(ennf_transformation,[],[f5])).
% 1.15/0.51  fof(f5,axiom,(
% 1.15/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.15/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.15/0.51  fof(f47,plain,(
% 1.15/0.51    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 1.15/0.51    inference(resolution,[],[f20,f22])).
% 1.15/0.51  fof(f22,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f12])).
% 1.15/0.51  fof(f57,plain,(
% 1.15/0.51    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.15/0.51    inference(superposition,[],[f19,f43])).
% 1.15/0.51  fof(f43,plain,(
% 1.15/0.51    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 1.15/0.51    inference(forward_demodulation,[],[f40,f38])).
% 1.15/0.51  fof(f38,plain,(
% 1.15/0.51    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)),
% 1.15/0.51    inference(resolution,[],[f17,f30])).
% 1.15/0.51  fof(f17,plain,(
% 1.15/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.15/0.51    inference(cnf_transformation,[],[f11])).
% 1.15/0.51  fof(f40,plain,(
% 1.15/0.51    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 1.15/0.51    inference(resolution,[],[f17,f22])).
% 1.15/0.51  fof(f19,plain,(
% 1.15/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.15/0.51    inference(cnf_transformation,[],[f11])).
% 1.15/0.51  fof(f36,plain,(
% 1.15/0.51    ~r1_tarski(sK2,sK1) | sK1 = sK2),
% 1.15/0.51    inference(resolution,[],[f18,f27])).
% 1.15/0.51  fof(f27,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.15/0.51    inference(cnf_transformation,[],[f1])).
% 1.15/0.51  fof(f20,plain,(
% 1.15/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.15/0.51    inference(cnf_transformation,[],[f11])).
% 1.15/0.51  fof(f121,plain,(
% 1.15/0.51    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)),
% 1.15/0.51    inference(forward_demodulation,[],[f107,f108])).
% 1.15/0.51  fof(f108,plain,(
% 1.15/0.51    k1_xboole_0 = sK2),
% 1.15/0.51    inference(subsumption_resolution,[],[f106,f58])).
% 1.15/0.51  fof(f58,plain,(
% 1.15/0.51    r1_tarski(k1_setfam_1(sK2),sK0)),
% 1.15/0.51    inference(resolution,[],[f42,f24])).
% 1.15/0.51  fof(f24,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f6])).
% 1.15/0.51  fof(f6,axiom,(
% 1.15/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.15/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.15/0.51  fof(f42,plain,(
% 1.15/0.51    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 1.15/0.51    inference(forward_demodulation,[],[f39,f38])).
% 1.15/0.51  fof(f39,plain,(
% 1.15/0.51    m1_subset_1(k6_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.15/0.51    inference(resolution,[],[f17,f29])).
% 1.15/0.51  fof(f29,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.15/0.51    inference(cnf_transformation,[],[f13])).
% 1.15/0.51  fof(f13,plain,(
% 1.15/0.51    ! [X0,X1] : (m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.15/0.51    inference(ennf_transformation,[],[f4])).
% 1.15/0.51  fof(f4,axiom,(
% 1.15/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.15/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).
% 1.15/0.51  fof(f106,plain,(
% 1.15/0.51    ~r1_tarski(k1_setfam_1(sK2),sK0) | k1_xboole_0 = sK2),
% 1.15/0.51    inference(backward_demodulation,[],[f93,f101])).
% 1.15/0.51  fof(f93,plain,(
% 1.15/0.51    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | k1_xboole_0 = sK2),
% 1.15/0.51    inference(backward_demodulation,[],[f57,f83])).
% 1.15/0.51  fof(f107,plain,(
% 1.15/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 1.15/0.51    inference(backward_demodulation,[],[f85,f101])).
% 1.15/0.51  fof(f85,plain,(
% 1.15/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 1.15/0.51    inference(backward_demodulation,[],[f19,f83])).
% 1.15/0.51  % SZS output end Proof for theBenchmark
% 1.15/0.51  % (9854)------------------------------
% 1.15/0.51  % (9854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.51  % (9854)Termination reason: Refutation
% 1.15/0.51  
% 1.15/0.51  % (9854)Memory used [KB]: 6140
% 1.15/0.51  % (9854)Time elapsed: 0.097 s
% 1.15/0.51  % (9854)------------------------------
% 1.15/0.51  % (9854)------------------------------
% 1.15/0.51  % (9871)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.15/0.52  % (9848)Success in time 0.147 s
%------------------------------------------------------------------------------
