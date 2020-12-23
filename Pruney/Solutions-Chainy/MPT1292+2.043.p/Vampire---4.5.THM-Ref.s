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
% DateTime   : Thu Dec  3 13:13:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  73 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 225 expanded)
%              Number of equality atoms :   22 (  52 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(subsumption_resolution,[],[f58,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(f58,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f57,f24])).

fof(f24,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f56,f37])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f33,f36])).

fof(f36,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f27,f33])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f33,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f56,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f28,f51])).

fof(f51,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f50,f43])).

fof(f43,plain,(
    k1_xboole_0 = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f41,f25])).

fof(f25,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f41,plain,(
    k3_tarski(k1_xboole_0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(resolution,[],[f29,f35])).

fof(f35,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f20,f22])).

fof(f22,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f50,plain,(
    u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f48,f34])).

fof(f34,plain,(
    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f21,f22])).

fof(f21,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,
    ( u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(resolution,[],[f31,f35])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = X0
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:49:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (7163)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (7160)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.43  % (7160)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f58,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ~v2_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f9])).
% 0.21/0.43  fof(f9,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f57,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    l1_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f56,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(superposition,[],[f33,f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    k1_xboole_0 = sK2),
% 0.21/0.43    inference(resolution,[],[f27,f33])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    v1_xboole_0(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(superposition,[],[f28,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(forward_demodulation,[],[f50,f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    k1_xboole_0 = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.43    inference(forward_demodulation,[],[f41,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    k3_tarski(k1_xboole_0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.43    inference(resolution,[],[f29,f35])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    inference(forward_demodulation,[],[f20,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    k1_xboole_0 = sK1),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k5_setfam_1(X0,X1) = k3_tarski(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (k5_setfam_1(X0,X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k5_setfam_1(X0,X1) = k3_tarski(X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f48,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.43    inference(forward_demodulation,[],[f21,f22])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) | ~m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.43    inference(resolution,[],[f31,f35])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (7160)------------------------------
% 0.21/0.43  % (7160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (7160)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (7160)Memory used [KB]: 10490
% 0.21/0.43  % (7160)Time elapsed: 0.006 s
% 0.21/0.43  % (7160)------------------------------
% 0.21/0.43  % (7160)------------------------------
% 0.21/0.43  % (7156)Success in time 0.068 s
%------------------------------------------------------------------------------
