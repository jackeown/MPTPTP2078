%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  47 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f34])).

fof(f34,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f22,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) ),
    inference(subsumption_resolution,[],[f32,f14])).

fof(f14,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0)))
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f31,f23])).

fof(f23,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f15,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f13,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(k9_setfam_1(X0))
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0)))
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f17,f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k9_setfam_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f18,f15])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f17,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f22,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f12,f16])).

fof(f16,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f12,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:04:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (26079)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.47  % (26079)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    k1_xboole_0 != k1_xboole_0),
% 0.22/0.47    inference(superposition,[],[f22,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f32,f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) | ~r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f31,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f13,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0] : (v1_xboole_0(k9_setfam_1(X0)) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(k9_setfam_1(X0))) | ~r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(resolution,[],[f17,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X2,X0] : (r2_hidden(X2,k9_setfam_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.22/0.47    inference(equality_resolution,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k9_setfam_1(X0) != X1) )),
% 0.22/0.47    inference(definition_unfolding,[],[f18,f15])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.22/0.47    inference(definition_unfolding,[],[f12,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (26079)------------------------------
% 0.22/0.47  % (26079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26079)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (26079)Memory used [KB]: 6140
% 0.22/0.47  % (26079)Time elapsed: 0.058 s
% 0.22/0.47  % (26079)------------------------------
% 0.22/0.47  % (26079)------------------------------
% 0.22/0.48  % (26072)Success in time 0.115 s
%------------------------------------------------------------------------------
