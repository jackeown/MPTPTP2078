%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  56 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   12
%              Number of atoms          :   78 ( 148 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(subsumption_resolution,[],[f40,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(f40,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f39,f22])).

fof(f22,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f38,f31])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f27,f30])).

fof(f30,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f24,f27])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f27,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] : v1_xboole_0(X1) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f38,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f26,f35])).

fof(f35,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f34,plain,(
    r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f19,f20])).

fof(f20,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(k1_xboole_0,X0)
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f28,f23])).

fof(f23,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:15:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (13385)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.41  % (13385)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(subsumption_resolution,[],[f40,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ~v2_struct_0(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.20/0.41    inference(flattening,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))))),
% 0.20/0.41    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.41  fof(f8,negated_conjecture,(
% 0.20/0.41    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.20/0.41    inference(negated_conjecture,[],[f7])).
% 0.20/0.41  fof(f7,conjecture,(
% 0.20/0.41    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    v2_struct_0(sK0)),
% 0.20/0.41    inference(subsumption_resolution,[],[f39,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    l1_struct_0(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.41    inference(subsumption_resolution,[],[f38,f31])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    v1_xboole_0(k1_xboole_0)),
% 0.20/0.41    inference(superposition,[],[f27,f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    k1_xboole_0 = sK2),
% 0.20/0.41    inference(resolution,[],[f24,f27])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    v1_xboole_0(sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0] : ? [X1] : v1_xboole_0(X1)),
% 0.20/0.41    inference(pure_predicate_removal,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.41    inference(superposition,[],[f26,f35])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    k1_xboole_0 = u1_struct_0(sK0)),
% 0.20/0.41    inference(resolution,[],[f34,f25])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    r1_tarski(u1_struct_0(sK0),k1_xboole_0)),
% 0.20/0.41    inference(resolution,[],[f33,f29])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.20/0.41    inference(forward_demodulation,[],[f19,f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    k1_xboole_0 = sK1),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_setfam_1(k1_xboole_0,X0) | r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.41    inference(superposition,[],[f28,f23])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.41    inference(cnf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0,X1] : (m1_setfam_1(X1,X0) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.41    inference(unused_predicate_definition_removal,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.41    inference(flattening,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (13385)------------------------------
% 0.20/0.41  % (13385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (13385)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (13385)Memory used [KB]: 10490
% 0.20/0.41  % (13385)Time elapsed: 0.003 s
% 0.20/0.41  % (13385)------------------------------
% 0.20/0.41  % (13385)------------------------------
% 0.20/0.41  % (13384)Success in time 0.05 s
%------------------------------------------------------------------------------
