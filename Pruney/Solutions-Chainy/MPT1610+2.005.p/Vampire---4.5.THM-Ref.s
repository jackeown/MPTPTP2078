%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 (  96 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f41,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(subsumption_resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
      | v1_xboole_0(k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(subsumption_resolution,[],[f53,f42])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(k9_setfam_1(X0))
      | r2_hidden(k1_xboole_0,k9_setfam_1(X0)) ) ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(backward_demodulation,[],[f44,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = sK2(X0) ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,(
    ! [X0] : v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2(X0))
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f43,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | k1_xboole_0 = k3_yellow_0(g1_orders_2(X0,k1_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f32,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f41,plain,(
    k1_xboole_0 != k3_yellow_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f40,plain,(
    ! [X0] : k3_yellow_1(X0) = g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f27,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).

fof(f19,plain,
    ( ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))
   => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (23518)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.43  % (23518)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0),
% 0.21/0.43    inference(superposition,[],[f41,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f56,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f29,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) | v1_xboole_0(k9_setfam_1(X0))) )),
% 0.21/0.43    inference(resolution,[],[f43,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(k1_xboole_0,k9_setfam_1(X0))) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f53,f42])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X0] : (v1_xboole_0(k9_setfam_1(X0)) | r2_hidden(k1_xboole_0,k9_setfam_1(X0))) )),
% 0.21/0.43    inference(resolution,[],[f38,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k9_setfam_1(X0))) )),
% 0.21/0.43    inference(backward_demodulation,[],[f44,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = sK2(X0)) )),
% 0.21/0.43    inference(resolution,[],[f46,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X0] : (v1_xboole_0(sK2(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(resolution,[],[f39,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(sK2(X0),k9_setfam_1(X0))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f36,f30])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_xboole_0 = k3_yellow_0(g1_orders_2(X0,k1_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f33,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    k1_xboole_0 != k3_yellow_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0))))),
% 0.21/0.43    inference(definition_unfolding,[],[f27,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0] : (k3_yellow_1(X0) = g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f31,f32])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,negated_conjecture,(
% 0.21/0.43    ~! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.21/0.43    inference(negated_conjecture,[],[f11])).
% 0.21/0.43  fof(f11,conjecture,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (23518)------------------------------
% 0.21/0.43  % (23518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (23518)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (23518)Memory used [KB]: 6140
% 0.21/0.43  % (23518)Time elapsed: 0.007 s
% 0.21/0.43  % (23518)------------------------------
% 0.21/0.43  % (23518)------------------------------
% 0.21/0.43  % (23510)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.43  % (23503)Success in time 0.08 s
%------------------------------------------------------------------------------
