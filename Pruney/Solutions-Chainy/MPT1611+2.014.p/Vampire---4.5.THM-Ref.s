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
% DateTime   : Thu Dec  3 13:16:41 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   56 (  73 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 (  94 expanded)
%              Number of equality atoms :   43 (  57 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f64])).

fof(f64,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f48,f62])).

fof(f62,plain,(
    ! [X0] : k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 ),
    inference(resolution,[],[f60,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k9_setfam_1(X0))
      | k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 ) ),
    inference(subsumption_resolution,[],[f56,f49])).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f32,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f30,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k9_setfam_1(X0))
      | k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(superposition,[],[f36,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k9_setfam_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f33,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f36,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f60,plain,(
    ! [X0] : r2_hidden(X0,k9_setfam_1(X0)) ),
    inference(superposition,[],[f55,f59])).

fof(f59,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f58,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k6_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[],[f53,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f31,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f53,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f40,f47])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : r2_hidden(k6_subset_1(X0,X1),k9_setfam_1(X0)) ),
    inference(subsumption_resolution,[],[f54,f49])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k9_setfam_1(X0))
      | r2_hidden(k6_subset_1(X0,X1),k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f44,f52])).

fof(f52,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f39,f32])).

fof(f39,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f48,plain,(
    sK0 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f35,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f29,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f23])).

fof(f23,plain,
    ( ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0
   => sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (784793601)
% 0.14/0.38  ipcrm: permission denied for id (784826372)
% 0.14/0.41  ipcrm: permission denied for id (784859162)
% 0.22/0.48  ipcrm: permission denied for id (784924743)
% 0.22/0.52  ipcrm: permission denied for id (784957555)
% 0.22/0.53  ipcrm: permission denied for id (785023100)
% 0.22/0.53  ipcrm: permission denied for id (785088638)
% 0.56/0.59  % (10259)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.56/0.59  % (10259)Refutation found. Thanks to Tanya!
% 0.56/0.59  % SZS status Theorem for theBenchmark
% 0.56/0.59  % SZS output start Proof for theBenchmark
% 0.56/0.59  fof(f65,plain,(
% 0.56/0.59    $false),
% 0.56/0.59    inference(trivial_inequality_removal,[],[f64])).
% 0.56/0.59  fof(f64,plain,(
% 0.56/0.59    sK0 != sK0),
% 0.56/0.59    inference(superposition,[],[f48,f62])).
% 0.56/0.59  fof(f62,plain,(
% 0.56/0.59    ( ! [X0] : (k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0) )),
% 0.56/0.59    inference(resolution,[],[f60,f57])).
% 0.56/0.59  fof(f57,plain,(
% 0.56/0.59    ( ! [X0] : (~r2_hidden(X0,k9_setfam_1(X0)) | k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0) )),
% 0.56/0.59    inference(subsumption_resolution,[],[f56,f49])).
% 0.56/0.59  fof(f49,plain,(
% 0.56/0.59    ( ! [X0] : (~v1_xboole_0(k9_setfam_1(X0))) )),
% 0.56/0.59    inference(definition_unfolding,[],[f30,f32])).
% 0.56/0.59  fof(f32,plain,(
% 0.56/0.59    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.56/0.59    inference(cnf_transformation,[],[f13])).
% 0.56/0.59  fof(f13,axiom,(
% 0.56/0.59    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.56/0.59  fof(f30,plain,(
% 0.56/0.59    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.56/0.59    inference(cnf_transformation,[],[f9])).
% 0.56/0.59  fof(f9,axiom,(
% 0.56/0.59    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.56/0.59  fof(f56,plain,(
% 0.56/0.59    ( ! [X0] : (~r2_hidden(X0,k9_setfam_1(X0)) | k4_yellow_0(k2_yellow_1(k9_setfam_1(X0))) = X0 | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.56/0.59    inference(superposition,[],[f36,f51])).
% 0.56/0.59  fof(f51,plain,(
% 0.56/0.59    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = X0) )),
% 0.56/0.59    inference(definition_unfolding,[],[f33,f32])).
% 0.56/0.59  fof(f33,plain,(
% 0.56/0.59    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.56/0.59    inference(cnf_transformation,[],[f7])).
% 0.56/0.59  fof(f7,axiom,(
% 0.56/0.59    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.56/0.59  fof(f36,plain,(
% 0.56/0.59    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.56/0.59    inference(cnf_transformation,[],[f20])).
% 0.56/0.59  fof(f20,plain,(
% 0.56/0.59    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.56/0.59    inference(flattening,[],[f19])).
% 0.56/0.59  fof(f19,plain,(
% 0.56/0.59    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.56/0.59    inference(ennf_transformation,[],[f14])).
% 0.56/0.59  fof(f14,axiom,(
% 0.56/0.59    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.56/0.59  fof(f60,plain,(
% 0.56/0.59    ( ! [X0] : (r2_hidden(X0,k9_setfam_1(X0))) )),
% 0.56/0.59    inference(superposition,[],[f55,f59])).
% 0.56/0.59  fof(f59,plain,(
% 0.56/0.59    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.56/0.59    inference(forward_demodulation,[],[f58,f34])).
% 0.56/0.59  fof(f34,plain,(
% 0.56/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.56/0.59    inference(cnf_transformation,[],[f4])).
% 0.56/0.59  fof(f4,axiom,(
% 0.56/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.56/0.59  fof(f58,plain,(
% 0.56/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k6_subset_1(X0,k1_xboole_0)) )),
% 0.56/0.59    inference(superposition,[],[f53,f50])).
% 0.56/0.59  fof(f50,plain,(
% 0.56/0.59    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) )),
% 0.56/0.59    inference(definition_unfolding,[],[f31,f47])).
% 0.56/0.59  fof(f47,plain,(
% 0.56/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.56/0.59    inference(definition_unfolding,[],[f41,f46])).
% 0.56/0.59  fof(f46,plain,(
% 0.56/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.56/0.59    inference(definition_unfolding,[],[f42,f45])).
% 0.56/0.59  fof(f45,plain,(
% 0.56/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.56/0.59    inference(cnf_transformation,[],[f6])).
% 0.56/0.59  fof(f6,axiom,(
% 0.56/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.56/0.59  fof(f42,plain,(
% 0.56/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.56/0.59    inference(cnf_transformation,[],[f5])).
% 0.56/0.59  fof(f5,axiom,(
% 0.56/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.56/0.59  fof(f41,plain,(
% 0.56/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.56/0.59    inference(cnf_transformation,[],[f11])).
% 0.56/0.59  fof(f11,axiom,(
% 0.56/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.56/0.60  fof(f31,plain,(
% 0.56/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.56/0.60    inference(cnf_transformation,[],[f3])).
% 0.56/0.60  fof(f3,axiom,(
% 0.56/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.56/0.60  fof(f53,plain,(
% 0.56/0.60    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.56/0.60    inference(definition_unfolding,[],[f43,f40,f47])).
% 0.56/0.60  fof(f40,plain,(
% 0.56/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.56/0.60    inference(cnf_transformation,[],[f10])).
% 0.56/0.60  fof(f10,axiom,(
% 0.56/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.56/0.60  fof(f43,plain,(
% 0.56/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.56/0.60    inference(cnf_transformation,[],[f2])).
% 0.56/0.60  fof(f2,axiom,(
% 0.56/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.56/0.60  fof(f55,plain,(
% 0.56/0.60    ( ! [X0,X1] : (r2_hidden(k6_subset_1(X0,X1),k9_setfam_1(X0))) )),
% 0.56/0.60    inference(subsumption_resolution,[],[f54,f49])).
% 0.56/0.60  fof(f54,plain,(
% 0.56/0.60    ( ! [X0,X1] : (v1_xboole_0(k9_setfam_1(X0)) | r2_hidden(k6_subset_1(X0,X1),k9_setfam_1(X0))) )),
% 0.56/0.60    inference(resolution,[],[f44,f52])).
% 0.56/0.60  fof(f52,plain,(
% 0.56/0.60    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k9_setfam_1(X0))) )),
% 0.56/0.60    inference(definition_unfolding,[],[f39,f32])).
% 0.56/0.60  fof(f39,plain,(
% 0.56/0.60    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.56/0.60    inference(cnf_transformation,[],[f8])).
% 0.56/0.60  fof(f8,axiom,(
% 0.56/0.60    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.56/0.60  fof(f44,plain,(
% 0.56/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.56/0.60    inference(cnf_transformation,[],[f22])).
% 0.56/0.60  fof(f22,plain,(
% 0.56/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.56/0.60    inference(flattening,[],[f21])).
% 0.56/0.60  fof(f21,plain,(
% 0.56/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.56/0.60    inference(ennf_transformation,[],[f12])).
% 0.56/0.60  fof(f12,axiom,(
% 0.56/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.56/0.60  fof(f48,plain,(
% 0.56/0.60    sK0 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.56/0.60    inference(definition_unfolding,[],[f29,f35])).
% 0.56/0.60  fof(f35,plain,(
% 0.56/0.60    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.56/0.60    inference(cnf_transformation,[],[f15])).
% 0.56/0.60  fof(f15,axiom,(
% 0.56/0.60    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.56/0.60  fof(f29,plain,(
% 0.56/0.60    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.56/0.60    inference(cnf_transformation,[],[f24])).
% 0.56/0.60  fof(f24,plain,(
% 0.56/0.60    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.56/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f23])).
% 0.56/0.60  fof(f23,plain,(
% 0.56/0.60    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 => sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 0.56/0.60    introduced(choice_axiom,[])).
% 0.56/0.60  fof(f18,plain,(
% 0.56/0.60    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0),
% 0.56/0.60    inference(ennf_transformation,[],[f17])).
% 0.56/0.60  fof(f17,negated_conjecture,(
% 0.56/0.60    ~! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.56/0.60    inference(negated_conjecture,[],[f16])).
% 0.56/0.60  fof(f16,conjecture,(
% 0.56/0.60    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 0.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).
% 0.56/0.60  % SZS output end Proof for theBenchmark
% 0.56/0.60  % (10259)------------------------------
% 0.56/0.60  % (10259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.56/0.60  % (10259)Termination reason: Refutation
% 0.56/0.60  
% 0.56/0.60  % (10259)Memory used [KB]: 6140
% 0.56/0.60  % (10259)Time elapsed: 0.005 s
% 0.56/0.60  % (10259)------------------------------
% 0.56/0.60  % (10259)------------------------------
% 0.56/0.60  % (10101)Success in time 0.232 s
%------------------------------------------------------------------------------
