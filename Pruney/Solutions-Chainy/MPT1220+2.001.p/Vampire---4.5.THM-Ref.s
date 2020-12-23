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
% DateTime   : Thu Dec  3 13:10:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 (  86 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 171 expanded)
%              Number of equality atoms :   28 (  62 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(global_subsumption,[],[f23,f68])).

% (29952)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
fof(f68,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f65,f47])).

fof(f47,plain,(
    k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    inference(resolution,[],[f46,f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f25,f24])).

fof(f24,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f45,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f45,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_xboole_0(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f44,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f30,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f22,f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f31,f36])).

fof(f36,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f35,f22])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f26,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(f65,plain,(
    k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    inference(resolution,[],[f64,f34])).

fof(f64,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k2_xboole_0(X0,k2_pre_topc(sK0,X0)) ) ),
    inference(global_subsumption,[],[f22,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_pre_topc(sK0,X0) = k2_xboole_0(X0,k2_pre_topc(sK0,X0)) ) ),
    inference(superposition,[],[f40,f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k2_pre_topc(X1,X0) = k2_xboole_0(X0,k2_pre_topc(X1,X0)) ) ),
    inference(resolution,[],[f28,f30])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f23,plain,(
    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:36:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (29954)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.43  % (29948)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (29948)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(global_subsumption,[],[f23,f68])).
% 0.22/0.43  % (29952)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.22/0.43    inference(forward_demodulation,[],[f65,f47])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))),
% 0.22/0.43    inference(resolution,[],[f46,f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f25,f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f45,f29])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_xboole_0(k2_pre_topc(sK0,X0),k2_struct_0(sK0))) )),
% 0.22/0.43    inference(resolution,[],[f44,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.43    inference(resolution,[],[f30,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.43    inference(nnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.22/0.43    inference(global_subsumption,[],[f22,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.22/0.43    inference(superposition,[],[f31,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.43    inference(resolution,[],[f35,f22])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.43    inference(resolution,[],[f26,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,axiom,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(flattening,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    l1_pre_topc(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0)) => (k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.22/0.43    inference(negated_conjecture,[],[f10])).
% 0.22/0.43  fof(f10,conjecture,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))),
% 0.22/0.43    inference(resolution,[],[f64,f34])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_xboole_0(X0,k2_pre_topc(sK0,X0))) )),
% 0.22/0.44    inference(global_subsumption,[],[f22,f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,X0) = k2_xboole_0(X0,k2_pre_topc(sK0,X0))) )),
% 0.22/0.44    inference(superposition,[],[f40,f36])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k2_pre_topc(X1,X0) = k2_xboole_0(X0,k2_pre_topc(X1,X0))) )),
% 0.22/0.44    inference(resolution,[],[f28,f30])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (29948)------------------------------
% 0.22/0.44  % (29948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (29948)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (29948)Memory used [KB]: 6140
% 0.22/0.44  % (29948)Time elapsed: 0.027 s
% 0.22/0.44  % (29948)------------------------------
% 0.22/0.44  % (29948)------------------------------
% 0.22/0.44  % (29943)Success in time 0.077 s
%------------------------------------------------------------------------------
