%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  56 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f49,f29,f110])).

% (14889)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f110,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f104,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f104,plain,(
    ! [X2,X3] : r1_tarski(k2_wellord1(k1_wellord2(X2),X3),k2_zfmisc_1(X3,X3)) ),
    inference(superposition,[],[f52,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_wellord1(k1_wellord2(X0),X1) = k1_setfam_1(k2_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X1))) ),
    inference(resolution,[],[f46,f30])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(X1,X1))) ) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(f52,plain,(
    ! [X2,X1] : r1_tarski(k1_setfam_1(k2_tarski(X2,X1)),X1) ),
    inference(superposition,[],[f48,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f29,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).

fof(f19,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:43:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (14905)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (14897)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (14890)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (14897)Refutation not found, incomplete strategy% (14897)------------------------------
% 0.20/0.51  % (14897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14897)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14897)Memory used [KB]: 1663
% 0.20/0.51  % (14897)Time elapsed: 0.054 s
% 0.20/0.51  % (14897)------------------------------
% 0.20/0.51  % (14897)------------------------------
% 0.20/0.52  % (14887)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (14905)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (14892)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f49,f29,f110])).
% 0.20/0.52  % (14889)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) | ~r1_tarski(X1,X0)) )),
% 0.20/0.52    inference(superposition,[],[f104,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X2,X3] : (r1_tarski(k2_wellord1(k1_wellord2(X2),X3),k2_zfmisc_1(X3,X3))) )),
% 0.20/0.52    inference(superposition,[],[f52,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X0),X1) = k1_setfam_1(k2_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X1)))) )),
% 0.20/0.52    inference(resolution,[],[f46,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(X0,X1) = k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(X1,X1)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f31,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X2,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X2,X1)),X1)) )),
% 0.20/0.52    inference(superposition,[],[f48,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f35,f37])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (14905)------------------------------
% 0.20/0.52  % (14905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14905)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (14905)Memory used [KB]: 6268
% 0.20/0.52  % (14905)Time elapsed: 0.060 s
% 0.20/0.52  % (14905)------------------------------
% 0.20/0.52  % (14905)------------------------------
% 0.20/0.52  % (14882)Success in time 0.161 s
%------------------------------------------------------------------------------
