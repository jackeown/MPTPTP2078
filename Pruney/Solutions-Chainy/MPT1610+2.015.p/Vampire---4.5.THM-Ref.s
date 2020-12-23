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
% DateTime   : Thu Dec  3 13:16:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 130 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f70])).

fof(f70,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl3_1 ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f26,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f24,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f58,plain,
    ( v1_xboole_0(k9_setfam_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_1
  <=> v1_xboole_0(k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f65,plain,
    ( ~ m1_subset_1(k1_xboole_0,k9_setfam_1(sK0))
    | spl3_2 ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f33,f26])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f64,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl3_2 ),
    inference(resolution,[],[f62,f46])).

fof(f46,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k9_setfam_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f62,plain,
    ( ~ r2_hidden(k1_xboole_0,k9_setfam_1(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_2
  <=> r2_hidden(k1_xboole_0,k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f63,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f54,f60,f56])).

fof(f54,plain,
    ( ~ r2_hidden(k1_xboole_0,k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(resolution,[],[f49,f50])).

fof(f50,plain,(
    ! [X0] :
      ( sQ2_eqProxy(k1_xboole_0,k3_yellow_0(k2_yellow_1(X0)))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f28,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f49,plain,(
    ~ sQ2_eqProxy(k1_xboole_0,k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))) ),
    inference(equality_proxy_replacement,[],[f36,f48])).

fof(f36,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f27,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f23,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f16,plain,
    ( ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))
   => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:55:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (18614)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (18622)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (18622)Refutation not found, incomplete strategy% (18622)------------------------------
% 0.22/0.55  % (18622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18622)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18622)Memory used [KB]: 1663
% 0.22/0.55  % (18622)Time elapsed: 0.072 s
% 0.22/0.55  % (18622)------------------------------
% 0.22/0.55  % (18622)------------------------------
% 0.22/0.55  % (18606)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (18614)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f63,f68,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ~spl3_1),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    $false | ~spl3_1),
% 0.22/0.55    inference(resolution,[],[f58,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(k9_setfam_1(X0))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f24,f26])).
% 1.44/0.55  fof(f26,plain,(
% 1.44/0.55    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f6])).
% 1.44/0.55  fof(f6,axiom,(
% 1.44/0.55    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 1.44/0.55  fof(f24,plain,(
% 1.44/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f2])).
% 1.44/0.55  fof(f2,axiom,(
% 1.44/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.44/0.55  fof(f58,plain,(
% 1.44/0.55    v1_xboole_0(k9_setfam_1(sK0)) | ~spl3_1),
% 1.44/0.55    inference(avatar_component_clause,[],[f56])).
% 1.44/0.55  fof(f56,plain,(
% 1.44/0.55    spl3_1 <=> v1_xboole_0(k9_setfam_1(sK0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.44/0.55  fof(f68,plain,(
% 1.44/0.55    spl3_2),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f66])).
% 1.44/0.55  fof(f66,plain,(
% 1.44/0.55    $false | spl3_2),
% 1.44/0.55    inference(resolution,[],[f65,f38])).
% 1.44/0.55  fof(f38,plain,(
% 1.44/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k9_setfam_1(X0))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f25,f26])).
% 1.44/0.55  fof(f25,plain,(
% 1.44/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f3])).
% 1.44/0.55  fof(f3,axiom,(
% 1.44/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.44/0.55  fof(f65,plain,(
% 1.44/0.55    ~m1_subset_1(k1_xboole_0,k9_setfam_1(sK0)) | spl3_2),
% 1.44/0.55    inference(resolution,[],[f64,f44])).
% 1.44/0.55  fof(f44,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k9_setfam_1(X1))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f33,f26])).
% 1.44/0.55  fof(f33,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f22])).
% 1.44/0.55  fof(f22,plain,(
% 1.44/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.44/0.55    inference(nnf_transformation,[],[f4])).
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.44/0.55  fof(f64,plain,(
% 1.44/0.55    ~r1_tarski(k1_xboole_0,sK0) | spl3_2),
% 1.44/0.55    inference(resolution,[],[f62,f46])).
% 1.44/0.55  fof(f46,plain,(
% 1.44/0.55    ( ! [X0,X3] : (r2_hidden(X3,k9_setfam_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f41])).
% 1.44/0.55  fof(f41,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k9_setfam_1(X0) != X1) )),
% 1.44/0.55    inference(definition_unfolding,[],[f30,f26])).
% 1.44/0.55  fof(f30,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f21])).
% 1.44/0.55  fof(f21,plain,(
% 1.44/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 1.44/0.55  fof(f20,plain,(
% 1.44/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f19,plain,(
% 1.44/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.55    inference(rectify,[],[f18])).
% 1.44/0.55  fof(f18,plain,(
% 1.44/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.55    inference(nnf_transformation,[],[f1])).
% 1.44/0.55  fof(f1,axiom,(
% 1.44/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.44/0.55  fof(f62,plain,(
% 1.44/0.55    ~r2_hidden(k1_xboole_0,k9_setfam_1(sK0)) | spl3_2),
% 1.44/0.55    inference(avatar_component_clause,[],[f60])).
% 1.44/0.55  fof(f60,plain,(
% 1.44/0.55    spl3_2 <=> r2_hidden(k1_xboole_0,k9_setfam_1(sK0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.44/0.55  fof(f63,plain,(
% 1.44/0.55    spl3_1 | ~spl3_2),
% 1.44/0.55    inference(avatar_split_clause,[],[f54,f60,f56])).
% 1.44/0.55  fof(f54,plain,(
% 1.44/0.55    ~r2_hidden(k1_xboole_0,k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 1.44/0.55    inference(resolution,[],[f49,f50])).
% 1.44/0.55  fof(f50,plain,(
% 1.44/0.55    ( ! [X0] : (sQ2_eqProxy(k1_xboole_0,k3_yellow_0(k2_yellow_1(X0))) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 1.44/0.55    inference(equality_proxy_replacement,[],[f28,f48])).
% 1.44/0.55  fof(f48,plain,(
% 1.44/0.55    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 1.44/0.55    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 1.44/0.55  fof(f28,plain,(
% 1.44/0.55    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f13])).
% 1.44/0.55  fof(f13,plain,(
% 1.44/0.55    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 1.44/0.55    inference(flattening,[],[f12])).
% 1.44/0.55  fof(f12,plain,(
% 1.44/0.55    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f7])).
% 1.44/0.55  fof(f7,axiom,(
% 1.44/0.55    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 1.44/0.55  fof(f49,plain,(
% 1.44/0.55    ~sQ2_eqProxy(k1_xboole_0,k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0))))),
% 1.44/0.55    inference(equality_proxy_replacement,[],[f36,f48])).
% 1.44/0.55  fof(f36,plain,(
% 1.44/0.55    k1_xboole_0 != k3_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 1.44/0.55    inference(definition_unfolding,[],[f23,f27])).
% 1.44/0.55  fof(f27,plain,(
% 1.44/0.55    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f8])).
% 1.44/0.55  fof(f8,axiom,(
% 1.44/0.55    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 1.44/0.55  fof(f23,plain,(
% 1.44/0.55    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 1.44/0.55    inference(cnf_transformation,[],[f17])).
% 1.44/0.55  fof(f17,plain,(
% 1.44/0.55    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 1.44/0.55  fof(f16,plain,(
% 1.44/0.55    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f11,plain,(
% 1.44/0.55    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f10])).
% 1.44/0.55  fof(f10,negated_conjecture,(
% 1.44/0.55    ~! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 1.44/0.55    inference(negated_conjecture,[],[f9])).
% 1.44/0.55  fof(f9,conjecture,(
% 1.44/0.55    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).
% 1.44/0.55  % SZS output end Proof for theBenchmark
% 1.44/0.55  % (18614)------------------------------
% 1.44/0.55  % (18614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (18614)Termination reason: Refutation
% 1.44/0.55  
% 1.44/0.55  % (18614)Memory used [KB]: 6140
% 1.44/0.55  % (18614)Time elapsed: 0.077 s
% 1.44/0.55  % (18614)------------------------------
% 1.44/0.55  % (18614)------------------------------
% 1.44/0.55  % (18598)Success in time 0.183 s
%------------------------------------------------------------------------------
