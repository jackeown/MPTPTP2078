%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 171 expanded)
%              Number of leaves         :   10 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  114 ( 711 expanded)
%              Number of equality atoms :   30 ( 177 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(subsumption_resolution,[],[f55,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = X1
            & m1_setfam_1(X1,u1_struct_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(sK0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( k1_xboole_0 = X1
        & m1_setfam_1(X1,u1_struct_0(sK0))
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK1
      & m1_setfam_1(sK1,u1_struct_0(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

fof(f55,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f54,f22])).

fof(f22,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f53,f46])).

fof(f46,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f45,f44])).

fof(f44,plain,(
    o_0_0_xboole_0 = k1_struct_0(sK0) ),
    inference(resolution,[],[f41,f22])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | o_0_0_xboole_0 = k1_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f36,f34])).

fof(f34,plain,(
    o_0_0_xboole_0 = sK1 ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f36,plain,(
    ! [X0] :
      ( k1_struct_0(X0) = sK1
      | ~ l1_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f45,plain,(
    v1_xboole_0(k1_struct_0(sK0)) ),
    inference(resolution,[],[f28,f22])).

fof(f28,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_xboole_0(k1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

fof(f53,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f31,f49])).

fof(f49,plain,(
    o_0_0_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f48,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,o_0_0_xboole_0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f42,f34])).

fof(f42,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,sK1) ) ),
    inference(forward_demodulation,[],[f37,f34])).

fof(f37,plain,(
    ! [X0] :
      ( sK1 = X0
      | ~ r1_tarski(X0,sK1) ) ),
    inference(definition_unfolding,[],[f30,f25,f25])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f48,plain,(
    r1_tarski(u1_struct_0(sK0),o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f47,f39])).

fof(f39,plain,(
    o_0_0_xboole_0 = k3_tarski(o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f35,f34])).

fof(f35,plain,(
    sK1 = k3_tarski(sK1) ),
    inference(definition_unfolding,[],[f27,f25,f25])).

fof(f27,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f47,plain,(
    r1_tarski(u1_struct_0(sK0),k3_tarski(o_0_0_xboole_0)) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    m1_setfam_1(o_0_0_xboole_0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f24,f34])).

fof(f24,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X1,X0)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:43:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.41  % (9062)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.41  % (9062)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f56,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(subsumption_resolution,[],[f55,f21])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ~v2_struct_0(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.41    inference(flattening,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : ((k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,negated_conjecture,(
% 0.21/0.41    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.41    inference(negated_conjecture,[],[f8])).
% 0.21/0.41  fof(f8,conjecture,(
% 0.21/0.41    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).
% 0.21/0.41  fof(f55,plain,(
% 0.21/0.41    v2_struct_0(sK0)),
% 0.21/0.41    inference(subsumption_resolution,[],[f54,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    l1_struct_0(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.41    inference(subsumption_resolution,[],[f53,f46])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    v1_xboole_0(o_0_0_xboole_0)),
% 0.21/0.41    inference(forward_demodulation,[],[f45,f44])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    o_0_0_xboole_0 = k1_struct_0(sK0)),
% 0.21/0.41    inference(resolution,[],[f41,f22])).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    ( ! [X0] : (~l1_struct_0(X0) | o_0_0_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.41    inference(forward_demodulation,[],[f36,f34])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    o_0_0_xboole_0 = sK1),
% 0.21/0.41    inference(definition_unfolding,[],[f26,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    k1_xboole_0 = sK1),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ( ! [X0] : (k1_struct_0(X0) = sK1 | ~l1_struct_0(X0)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f29,f25])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    v1_xboole_0(k1_struct_0(sK0))),
% 0.21/0.41    inference(resolution,[],[f28,f22])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X0] : (~l1_struct_0(X0) | v1_xboole_0(k1_struct_0(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,axiom,(
% 0.21/0.41    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    ~v1_xboole_0(o_0_0_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.41    inference(superposition,[],[f31,f49])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    o_0_0_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.41    inference(resolution,[],[f48,f43])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(X0,o_0_0_xboole_0) | o_0_0_xboole_0 = X0) )),
% 0.21/0.41    inference(forward_demodulation,[],[f42,f34])).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    ( ! [X0] : (o_0_0_xboole_0 = X0 | ~r1_tarski(X0,sK1)) )),
% 0.21/0.41    inference(forward_demodulation,[],[f37,f34])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    ( ! [X0] : (sK1 = X0 | ~r1_tarski(X0,sK1)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f30,f25,f25])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    r1_tarski(u1_struct_0(sK0),o_0_0_xboole_0)),
% 0.21/0.41    inference(forward_demodulation,[],[f47,f39])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    o_0_0_xboole_0 = k3_tarski(o_0_0_xboole_0)),
% 0.21/0.41    inference(forward_demodulation,[],[f35,f34])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    sK1 = k3_tarski(sK1)),
% 0.21/0.41    inference(definition_unfolding,[],[f27,f25,f25])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    r1_tarski(u1_struct_0(sK0),k3_tarski(o_0_0_xboole_0))),
% 0.21/0.41    inference(resolution,[],[f32,f38])).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    m1_setfam_1(o_0_0_xboole_0,u1_struct_0(sK0))),
% 0.21/0.41    inference(forward_demodulation,[],[f24,f34])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~m1_setfam_1(X1,X0) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.21/0.41    inference(nnf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.41    inference(flattening,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (9062)------------------------------
% 0.21/0.41  % (9062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (9062)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (9062)Memory used [KB]: 1663
% 0.21/0.41  % (9062)Time elapsed: 0.005 s
% 0.21/0.41  % (9062)------------------------------
% 0.21/0.41  % (9062)------------------------------
% 0.21/0.41  % (9049)Success in time 0.058 s
%------------------------------------------------------------------------------
