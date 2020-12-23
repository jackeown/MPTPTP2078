%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:41 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   46 (  50 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 (  82 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f52])).

fof(f52,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f36,f51])).

fof(f51,plain,(
    ! [X0] : k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 ),
    inference(subsumption_resolution,[],[f50,f45])).

fof(f45,plain,(
    ! [X2] : r2_hidden(X2,k9_setfam_1(X2)) ),
    inference(subsumption_resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f26,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f25,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f43,plain,(
    ! [X2] :
      ( v1_xboole_0(k9_setfam_1(X2))
      | r2_hidden(X2,k9_setfam_1(X2)) ) ),
    inference(resolution,[],[f35,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(X0,k9_setfam_1(X0)) ),
    inference(superposition,[],[f39,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f39,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f33,f34,f26])).

fof(f34,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f33,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k9_setfam_1(X0))
      | k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 ) ),
    inference(superposition,[],[f49,f38])).

fof(f38,plain,(
    ! [X0] : k3_tarski(k9_setfam_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f30,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f36,plain,(
    sK0 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f29,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f24,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f18])).

fof(f18,plain,
    ( ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0
   => sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (7042)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.13/0.40  % (7042)Refutation found. Thanks to Tanya!
% 0.13/0.40  % SZS status Theorem for theBenchmark
% 0.13/0.40  % SZS output start Proof for theBenchmark
% 0.13/0.40  fof(f53,plain,(
% 0.13/0.40    $false),
% 0.13/0.40    inference(trivial_inequality_removal,[],[f52])).
% 0.13/0.40  fof(f52,plain,(
% 0.13/0.40    sK0 != sK0),
% 0.13/0.40    inference(superposition,[],[f36,f51])).
% 0.13/0.40  fof(f51,plain,(
% 0.13/0.40    ( ! [X0] : (k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0) )),
% 0.13/0.40    inference(subsumption_resolution,[],[f50,f45])).
% 0.13/0.40  fof(f45,plain,(
% 0.13/0.40    ( ! [X2] : (r2_hidden(X2,k9_setfam_1(X2))) )),
% 0.13/0.40    inference(subsumption_resolution,[],[f43,f37])).
% 0.13/0.40  fof(f37,plain,(
% 0.13/0.40    ( ! [X0] : (~v1_xboole_0(k9_setfam_1(X0))) )),
% 0.13/0.40    inference(definition_unfolding,[],[f25,f26])).
% 0.13/0.40  fof(f26,plain,(
% 0.13/0.40    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f8])).
% 0.13/0.40  fof(f8,axiom,(
% 0.13/0.40    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.13/0.40  fof(f25,plain,(
% 0.13/0.40    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.13/0.40    inference(cnf_transformation,[],[f5])).
% 0.13/0.40  fof(f5,axiom,(
% 0.13/0.40    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.13/0.40  fof(f43,plain,(
% 0.13/0.40    ( ! [X2] : (v1_xboole_0(k9_setfam_1(X2)) | r2_hidden(X2,k9_setfam_1(X2))) )),
% 0.13/0.40    inference(resolution,[],[f35,f41])).
% 0.13/0.40  fof(f41,plain,(
% 0.13/0.40    ( ! [X0] : (m1_subset_1(X0,k9_setfam_1(X0))) )),
% 0.13/0.40    inference(superposition,[],[f39,f28])).
% 0.13/0.40  fof(f28,plain,(
% 0.13/0.40    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.13/0.40    inference(cnf_transformation,[],[f2])).
% 0.13/0.40  fof(f2,axiom,(
% 0.13/0.40    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.13/0.40  fof(f39,plain,(
% 0.13/0.40    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k9_setfam_1(X0))) )),
% 0.13/0.40    inference(definition_unfolding,[],[f33,f34,f26])).
% 0.13/0.40  fof(f34,plain,(
% 0.13/0.40    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f6])).
% 0.13/0.40  fof(f6,axiom,(
% 0.13/0.40    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.13/0.40  fof(f33,plain,(
% 0.13/0.40    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.13/0.40    inference(cnf_transformation,[],[f4])).
% 0.13/0.40  fof(f4,axiom,(
% 0.13/0.40    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.13/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.13/0.40  fof(f35,plain,(
% 0.13/0.40    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.13/0.40    inference(cnf_transformation,[],[f17])).
% 0.13/0.41  fof(f17,plain,(
% 0.13/0.41    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.13/0.41    inference(flattening,[],[f16])).
% 0.13/0.41  fof(f16,plain,(
% 0.13/0.41    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f7])).
% 0.13/0.41  fof(f7,axiom,(
% 0.13/0.41    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.13/0.41  fof(f50,plain,(
% 0.13/0.41    ( ! [X0] : (~r2_hidden(X0,k9_setfam_1(X0)) | k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0) )),
% 0.13/0.41    inference(superposition,[],[f49,f38])).
% 0.13/0.41  fof(f38,plain,(
% 0.13/0.41    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = X0) )),
% 0.13/0.41    inference(definition_unfolding,[],[f27,f26])).
% 0.13/0.41  fof(f27,plain,(
% 0.13/0.41    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.13/0.41  fof(f49,plain,(
% 0.13/0.41    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 0.13/0.41    inference(subsumption_resolution,[],[f30,f31])).
% 0.13/0.41  fof(f31,plain,(
% 0.13/0.41    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f23])).
% 0.13/0.41  fof(f23,plain,(
% 0.13/0.41    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 0.13/0.41  fof(f22,plain,(
% 0.13/0.41    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.13/0.41    inference(rectify,[],[f20])).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.13/0.41    inference(nnf_transformation,[],[f1])).
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.13/0.41  fof(f30,plain,(
% 0.13/0.41    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f15])).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.13/0.41    inference(flattening,[],[f14])).
% 0.13/0.41  fof(f14,plain,(
% 0.13/0.41    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.13/0.41    inference(ennf_transformation,[],[f9])).
% 0.13/0.41  fof(f9,axiom,(
% 0.13/0.41    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.13/0.41  fof(f36,plain,(
% 0.13/0.41    sK0 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.13/0.41    inference(definition_unfolding,[],[f24,f29])).
% 0.13/0.41  fof(f29,plain,(
% 0.13/0.41    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f10])).
% 0.13/0.41  fof(f10,axiom,(
% 0.13/0.41    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.13/0.41  fof(f24,plain,(
% 0.13/0.41    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.13/0.41    inference(cnf_transformation,[],[f19])).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f18])).
% 0.13/0.41  fof(f18,plain,(
% 0.13/0.41    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 => sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f13,plain,(
% 0.13/0.41    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0),
% 0.13/0.41    inference(ennf_transformation,[],[f12])).
% 0.13/0.41  fof(f12,negated_conjecture,(
% 0.13/0.41    ~! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.13/0.41    inference(negated_conjecture,[],[f11])).
% 0.13/0.41  fof(f11,conjecture,(
% 0.13/0.41    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (7042)------------------------------
% 0.13/0.41  % (7042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (7042)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (7042)Memory used [KB]: 1535
% 0.13/0.41  % (7042)Time elapsed: 0.004 s
% 0.13/0.41  % (7042)------------------------------
% 0.13/0.41  % (7042)------------------------------
% 0.13/0.41  % (7029)Success in time 0.054 s
%------------------------------------------------------------------------------
