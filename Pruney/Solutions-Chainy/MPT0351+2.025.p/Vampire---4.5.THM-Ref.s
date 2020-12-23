%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:06 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 115 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 155 expanded)
%              Number of equality atoms :   43 ( 100 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(subsumption_resolution,[],[f144,f53])).

fof(f53,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f22,f24])).

fof(f24,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f22,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f144,plain,(
    sK0 = k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f143,f93])).

fof(f93,plain,(
    sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f89,f47])).

fof(f47,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f25,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f89,plain,(
    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k1_xboole_0)) ),
    inference(superposition,[],[f49,f65])).

fof(f65,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f39,f61])).

fof(f61,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f59,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f59,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f55,f23])).

fof(f23,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f55,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f34,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f30,f46,f46])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f143,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f140,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f45,f45])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f140,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK0)) ),
    inference(resolution,[],[f110,f21])).

fof(f110,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k4_subset_1(X2,X1,X2) ) ),
    inference(resolution,[],[f50,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f26,f24])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:20:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (6371)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (6372)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (6379)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (6380)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (6387)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.55  % (6388)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  % (6371)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.56  % (6387)Refutation not found, incomplete strategy% (6387)------------------------------
% 1.41/0.56  % (6387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (6373)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.57  % (6380)Refutation not found, incomplete strategy% (6380)------------------------------
% 1.41/0.57  % (6380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (6380)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (6380)Memory used [KB]: 6140
% 1.41/0.57  % (6380)Time elapsed: 0.003 s
% 1.41/0.57  % (6380)------------------------------
% 1.41/0.57  % (6380)------------------------------
% 1.41/0.57  % (6387)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (6387)Memory used [KB]: 10746
% 1.41/0.57  % (6387)Time elapsed: 0.125 s
% 1.41/0.57  % (6387)------------------------------
% 1.41/0.57  % (6387)------------------------------
% 1.41/0.57  % SZS output start Proof for theBenchmark
% 1.41/0.57  fof(f145,plain,(
% 1.41/0.57    $false),
% 1.41/0.57    inference(subsumption_resolution,[],[f144,f53])).
% 1.41/0.57  fof(f53,plain,(
% 1.41/0.57    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 1.41/0.57    inference(backward_demodulation,[],[f22,f24])).
% 1.41/0.57  fof(f24,plain,(
% 1.41/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.41/0.57    inference(cnf_transformation,[],[f11])).
% 1.41/0.57  fof(f11,axiom,(
% 1.41/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.41/0.57  fof(f22,plain,(
% 1.41/0.57    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.41/0.57    inference(cnf_transformation,[],[f17])).
% 1.41/0.57  fof(f17,plain,(
% 1.41/0.57    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f16])).
% 1.41/0.57  fof(f16,negated_conjecture,(
% 1.41/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.41/0.57    inference(negated_conjecture,[],[f15])).
% 1.41/0.57  fof(f15,conjecture,(
% 1.41/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 1.52/0.57  fof(f144,plain,(
% 1.52/0.57    sK0 = k4_subset_1(sK0,sK1,sK0)),
% 1.52/0.57    inference(forward_demodulation,[],[f143,f93])).
% 1.52/0.57  fof(f93,plain,(
% 1.52/0.57    sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 1.52/0.57    inference(forward_demodulation,[],[f89,f47])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f25,f46])).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f29,f45])).
% 1.52/0.57  fof(f45,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f28,f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f41,f43])).
% 1.52/0.57  fof(f43,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f7])).
% 1.52/0.57  fof(f7,axiom,(
% 1.52/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.52/0.57  fof(f89,plain,(
% 1.52/0.57    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k1_xboole_0))),
% 1.52/0.57    inference(superposition,[],[f49,f65])).
% 1.52/0.57  fof(f65,plain,(
% 1.52/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.52/0.57    inference(resolution,[],[f39,f61])).
% 1.52/0.57  fof(f61,plain,(
% 1.52/0.57    r1_tarski(sK1,sK0)),
% 1.52/0.57    inference(resolution,[],[f59,f51])).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f36])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,axiom,(
% 1.52/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(subsumption_resolution,[],[f55,f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f13])).
% 1.52/0.57  fof(f13,axiom,(
% 1.52/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.52/0.57  fof(f55,plain,(
% 1.52/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(resolution,[],[f34,f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f34,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f18])).
% 1.52/0.57  fof(f18,plain,(
% 1.52/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,axiom,(
% 1.52/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f30,f46,f46])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.52/0.57  fof(f143,plain,(
% 1.52/0.57    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 1.52/0.57    inference(forward_demodulation,[],[f140,f48])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f27,f45,f45])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.52/0.57  fof(f140,plain,(
% 1.52/0.57    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK0))),
% 1.52/0.57    inference(resolution,[],[f110,f21])).
% 1.52/0.57  fof(f110,plain,(
% 1.52/0.57    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k4_subset_1(X2,X1,X2)) )),
% 1.52/0.57    inference(resolution,[],[f50,f54])).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.52/0.57    inference(forward_demodulation,[],[f26,f24])).
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,axiom,(
% 1.52/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.52/0.57  fof(f50,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f42,f46])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.52/0.57    inference(flattening,[],[f19])).
% 1.52/0.57  fof(f19,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.52/0.57    inference(ennf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (6371)------------------------------
% 1.52/0.57  % (6371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (6371)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (6371)Memory used [KB]: 6268
% 1.52/0.57  % (6371)Time elapsed: 0.118 s
% 1.52/0.57  % (6371)------------------------------
% 1.52/0.57  % (6371)------------------------------
% 1.52/0.57  % (6364)Success in time 0.196 s
%------------------------------------------------------------------------------
