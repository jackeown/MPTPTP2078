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
% DateTime   : Thu Dec  3 13:13:14 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   39 (  68 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 262 expanded)
%              Number of equality atoms :   24 (  60 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f20,f25,f53])).

fof(f53,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f29,f43])).

fof(f43,plain,(
    k1_xboole_0 = k2_struct_0(sK0) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    m1_setfam_1(k1_xboole_0,k2_struct_0(sK0)) ),
    inference(superposition,[],[f33,f35])).

fof(f35,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f28,f21])).

fof(f28,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f33,plain,(
    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f23,f24])).

fof(f24,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 = sK1
    & m1_setfam_1(sK1,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(f23,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X2] :
      ( ~ m1_setfam_1(k1_xboole_0,X2)
      | k1_xboole_0 = X2 ) ),
    inference(forward_demodulation,[],[f40,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f40,plain,(
    ! [X2] :
      ( k3_xboole_0(X2,k1_xboole_0) = X2
      | ~ m1_setfam_1(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
      | ~ m1_setfam_1(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f31,f26])).

fof(f26,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:17:16 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.39  % (27912)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.17/0.39  % (27912)Refutation found. Thanks to Tanya!
% 0.17/0.39  % SZS status Theorem for theBenchmark
% 0.17/0.39  % SZS output start Proof for theBenchmark
% 0.17/0.39  fof(f54,plain,(
% 0.17/0.39    $false),
% 0.17/0.39    inference(global_subsumption,[],[f21,f20,f25,f53])).
% 0.17/0.39  fof(f53,plain,(
% 0.17/0.39    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.17/0.39    inference(superposition,[],[f29,f43])).
% 0.17/0.39  fof(f43,plain,(
% 0.17/0.39    k1_xboole_0 = k2_struct_0(sK0)),
% 0.17/0.39    inference(resolution,[],[f41,f37])).
% 0.17/0.39  fof(f37,plain,(
% 0.17/0.39    m1_setfam_1(k1_xboole_0,k2_struct_0(sK0))),
% 0.17/0.39    inference(superposition,[],[f33,f35])).
% 0.17/0.39  fof(f35,plain,(
% 0.17/0.39    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.17/0.39    inference(resolution,[],[f28,f21])).
% 0.17/0.39  fof(f28,plain,(
% 0.17/0.39    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.17/0.39    inference(cnf_transformation,[],[f12])).
% 0.17/0.39  fof(f12,plain,(
% 0.17/0.39    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.17/0.39    inference(ennf_transformation,[],[f6])).
% 0.17/0.39  fof(f6,axiom,(
% 0.17/0.39    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.17/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.17/0.39  fof(f33,plain,(
% 0.17/0.39    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.17/0.39    inference(forward_demodulation,[],[f23,f24])).
% 0.17/0.39  fof(f24,plain,(
% 0.17/0.39    k1_xboole_0 = sK1),
% 0.17/0.39    inference(cnf_transformation,[],[f18])).
% 0.17/0.39  fof(f18,plain,(
% 0.17/0.39    (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.17/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17,f16])).
% 0.17/0.39  fof(f16,plain,(
% 0.17/0.39    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.17/0.39    introduced(choice_axiom,[])).
% 0.17/0.39  fof(f17,plain,(
% 0.17/0.39    ? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK1 & m1_setfam_1(sK1,u1_struct_0(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.17/0.39    introduced(choice_axiom,[])).
% 0.17/0.39  fof(f11,plain,(
% 0.17/0.39    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.17/0.39    inference(flattening,[],[f10])).
% 0.17/0.39  fof(f10,plain,(
% 0.17/0.39    ? [X0] : (? [X1] : ((k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.17/0.39    inference(ennf_transformation,[],[f9])).
% 0.17/0.39  fof(f9,negated_conjecture,(
% 0.17/0.39    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.17/0.39    inference(negated_conjecture,[],[f8])).
% 0.17/0.39  fof(f8,conjecture,(
% 0.17/0.39    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.17/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).
% 0.17/0.39  fof(f23,plain,(
% 0.17/0.39    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.17/0.39    inference(cnf_transformation,[],[f18])).
% 0.17/0.39  fof(f41,plain,(
% 0.17/0.39    ( ! [X2] : (~m1_setfam_1(k1_xboole_0,X2) | k1_xboole_0 = X2) )),
% 0.17/0.39    inference(forward_demodulation,[],[f40,f27])).
% 0.17/0.39  fof(f27,plain,(
% 0.17/0.39    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.17/0.39    inference(cnf_transformation,[],[f3])).
% 0.17/0.39  fof(f3,axiom,(
% 0.17/0.39    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.17/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.17/0.39  fof(f40,plain,(
% 0.17/0.39    ( ! [X2] : (k3_xboole_0(X2,k1_xboole_0) = X2 | ~m1_setfam_1(k1_xboole_0,X2)) )),
% 0.17/0.39    inference(resolution,[],[f30,f38])).
% 0.17/0.39  fof(f38,plain,(
% 0.17/0.39    ( ! [X0] : (r1_tarski(X0,k1_xboole_0) | ~m1_setfam_1(k1_xboole_0,X0)) )),
% 0.17/0.39    inference(superposition,[],[f31,f26])).
% 0.17/0.39  fof(f26,plain,(
% 0.17/0.39    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.17/0.39    inference(cnf_transformation,[],[f4])).
% 0.17/0.39  fof(f4,axiom,(
% 0.17/0.39    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.17/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.17/0.39  fof(f31,plain,(
% 0.17/0.39    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.17/0.39    inference(cnf_transformation,[],[f19])).
% 0.17/0.39  fof(f19,plain,(
% 0.17/0.39    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.17/0.39    inference(nnf_transformation,[],[f5])).
% 0.17/0.39  fof(f5,axiom,(
% 0.17/0.39    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.17/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.17/0.39  fof(f30,plain,(
% 0.17/0.39    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.17/0.39    inference(cnf_transformation,[],[f15])).
% 0.17/0.39  fof(f15,plain,(
% 0.17/0.39    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.17/0.39    inference(ennf_transformation,[],[f2])).
% 0.17/0.39  fof(f2,axiom,(
% 0.17/0.39    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.17/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.17/0.39  fof(f29,plain,(
% 0.17/0.39    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.17/0.39    inference(cnf_transformation,[],[f14])).
% 0.17/0.39  fof(f14,plain,(
% 0.17/0.39    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.17/0.39    inference(flattening,[],[f13])).
% 0.17/0.39  fof(f13,plain,(
% 0.17/0.39    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.17/0.39    inference(ennf_transformation,[],[f7])).
% 0.17/0.39  fof(f7,axiom,(
% 0.17/0.39    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.17/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.17/0.39  fof(f25,plain,(
% 0.17/0.39    v1_xboole_0(k1_xboole_0)),
% 0.17/0.39    inference(cnf_transformation,[],[f1])).
% 0.17/0.39  fof(f1,axiom,(
% 0.17/0.39    v1_xboole_0(k1_xboole_0)),
% 0.17/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.17/0.39  fof(f20,plain,(
% 0.17/0.39    ~v2_struct_0(sK0)),
% 0.17/0.39    inference(cnf_transformation,[],[f18])).
% 0.17/0.39  fof(f21,plain,(
% 0.17/0.39    l1_struct_0(sK0)),
% 0.17/0.39    inference(cnf_transformation,[],[f18])).
% 0.17/0.39  % SZS output end Proof for theBenchmark
% 0.17/0.39  % (27912)------------------------------
% 0.17/0.39  % (27912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.39  % (27912)Termination reason: Refutation
% 0.17/0.39  
% 0.17/0.39  % (27912)Memory used [KB]: 6140
% 0.17/0.39  % (27912)Time elapsed: 0.005 s
% 0.17/0.39  % (27912)------------------------------
% 0.17/0.39  % (27912)------------------------------
% 0.17/0.39  % (27903)Success in time 0.064 s
%------------------------------------------------------------------------------
