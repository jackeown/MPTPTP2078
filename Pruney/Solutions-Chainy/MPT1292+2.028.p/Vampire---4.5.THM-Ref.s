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
% DateTime   : Thu Dec  3 13:13:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  62 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 202 expanded)
%              Number of equality atoms :   20 (  50 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0)) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

fof(f56,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f28,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f54,f31])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f54,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f34,f49])).

fof(f49,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    inference(resolution,[],[f45,f44])).

fof(f44,plain,(
    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f29,f30])).

fof(f30,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0] :
      ( ~ m1_setfam_1(k1_xboole_0,X0)
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f38,f32])).

fof(f32,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f37,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:13:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (23338)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.43  % (23338)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f56,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ~v2_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))))),
% 0.21/0.43    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.43  fof(f15,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f14])).
% 0.21/0.43  fof(f14,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f55,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    l1_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f54,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(superposition,[],[f34,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f47,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    r1_tarski(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.43    inference(resolution,[],[f45,f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.43    inference(forward_demodulation,[],[f29,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    k1_xboole_0 = sK1),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_setfam_1(k1_xboole_0,X0) | r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(superposition,[],[f38,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_setfam_1(X1,X0) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.43    inference(unused_predicate_definition_removal,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(superposition,[],[f37,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,axiom,(
% 0.21/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (23338)------------------------------
% 0.21/0.43  % (23338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (23338)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (23338)Memory used [KB]: 1663
% 0.21/0.43  % (23338)Time elapsed: 0.004 s
% 0.21/0.43  % (23338)------------------------------
% 0.21/0.43  % (23338)------------------------------
% 0.21/0.44  % (23331)Success in time 0.073 s
%------------------------------------------------------------------------------
