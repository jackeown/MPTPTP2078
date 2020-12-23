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
% DateTime   : Thu Dec  3 13:16:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  51 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 (  83 expanded)
%              Number of equality atoms :   33 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38,f86])).

fof(f86,plain,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | k4_yellow_0(k3_yellow_1(X0)) = X0 ) ),
    inference(resolution,[],[f82,f67])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f52,f66])).

fof(f66,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f63,f43])).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f63,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f53,f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
      | k4_yellow_0(k3_yellow_1(X0)) = X0 ) ),
    inference(resolution,[],[f81,f39])).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f81,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | k4_yellow_0(k3_yellow_1(X0)) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f80,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f80,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X0))
      | k4_yellow_0(k3_yellow_1(X0)) = X0 ) ),
    inference(forward_demodulation,[],[f79,f42])).

fof(f42,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f79,plain,(
    ! [X0] :
      ( k3_tarski(k1_zfmisc_1(X0)) = k4_yellow_0(k3_yellow_1(X0))
      | ~ r2_hidden(X0,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f78,f60])).

fof(f60,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f44,f41])).

fof(f41,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f44,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X0))
      | k3_tarski(k1_zfmisc_1(X0)) = k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X0))) ) ),
    inference(forward_demodulation,[],[f77,f42])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(k1_zfmisc_1(X0)),k1_zfmisc_1(X0))
      | k3_tarski(k1_zfmisc_1(X0)) = k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f45,f39])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f38,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f32])).

fof(f32,plain,
    ( ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0
   => sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:09:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (11637)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.45  % (11637)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(subsumption_resolution,[],[f38,f86])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    ( ! [X0] : (k4_yellow_0(k3_yellow_1(X0)) = X0) )),
% 0.22/0.45    inference(resolution,[],[f83,f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,axiom,(
% 0.22/0.45    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.45  fof(f83,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | k4_yellow_0(k3_yellow_1(X0)) = X0) )),
% 0.22/0.45    inference(resolution,[],[f82,f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(superposition,[],[f52,f66])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.45    inference(forward_demodulation,[],[f63,f43])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.45    inference(resolution,[],[f53,f40])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,axiom,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,axiom,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(X0)) | k4_yellow_0(k3_yellow_1(X0)) = X0) )),
% 0.22/0.45    inference(resolution,[],[f81,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,axiom,(
% 0.22/0.45    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.45  fof(f81,plain,(
% 0.22/0.45    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | k4_yellow_0(k3_yellow_1(X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(resolution,[],[f80,f51])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,axiom,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(X0)) | k4_yellow_0(k3_yellow_1(X0)) = X0) )),
% 0.22/0.45    inference(forward_demodulation,[],[f79,f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,axiom,(
% 0.22/0.45    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.45  fof(f79,plain,(
% 0.22/0.45    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = k4_yellow_0(k3_yellow_1(X0)) | ~r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f78,f60])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f44,f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,axiom,(
% 0.22/0.45    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,axiom,(
% 0.22/0.45    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(X0)) | k3_tarski(k1_zfmisc_1(X0)) = k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f77,f42])).
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(k3_tarski(k1_zfmisc_1(X0)),k1_zfmisc_1(X0)) | k3_tarski(k1_zfmisc_1(X0)) = k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.45    inference(resolution,[],[f45,f39])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X0] : (v1_xboole_0(X0) | ~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,axiom,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 => sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0),
% 0.22/0.45    inference(ennf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,negated_conjecture,(
% 0.22/0.45    ~! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.22/0.45    inference(negated_conjecture,[],[f21])).
% 0.22/0.45  fof(f21,conjecture,(
% 0.22/0.45    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (11637)------------------------------
% 0.22/0.45  % (11637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (11637)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (11637)Memory used [KB]: 6140
% 0.22/0.45  % (11637)Time elapsed: 0.006 s
% 0.22/0.45  % (11637)------------------------------
% 0.22/0.45  % (11637)------------------------------
% 0.22/0.45  % (11620)Success in time 0.087 s
%------------------------------------------------------------------------------
