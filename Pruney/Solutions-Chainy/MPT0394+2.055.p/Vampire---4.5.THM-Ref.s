%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  77 expanded)
%              Number of equality atoms :   48 (  60 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f170,f181])).

fof(f181,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_1 ),
    inference(superposition,[],[f22,f154])).

fof(f154,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl2_1
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[],[f21,f15])).

fof(f15,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) != k1_xboole_0 ),
    inference(superposition,[],[f19,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f170,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_2 ),
    inference(superposition,[],[f22,f158])).

fof(f158,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f159,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f148,f156,f152])).

fof(f148,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)
    | k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f13,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
      | k1_tarski(X1) = k1_xboole_0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(forward_demodulation,[],[f96,f14])).

fof(f14,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1)))
      | k1_tarski(X1) = k1_xboole_0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f25,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f18,f14])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f13,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:55:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (2681)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.44  % (2681)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f159,f170,f181])).
% 0.21/0.44  fof(f181,plain,(
% 0.21/0.44    ~spl2_1),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f180])).
% 0.21/0.44  fof(f180,plain,(
% 0.21/0.44    $false | ~spl2_1),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f175])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | ~spl2_1),
% 0.21/0.44    inference(superposition,[],[f22,f154])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    k1_xboole_0 = k1_tarski(sK0) | ~spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f152])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    spl2_1 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) != k1_xboole_0) )),
% 0.21/0.44    inference(superposition,[],[f21,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) != k1_xboole_0) )),
% 0.21/0.44    inference(superposition,[],[f19,f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    ~spl2_2),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f169])).
% 0.21/0.44  fof(f169,plain,(
% 0.21/0.44    $false | ~spl2_2),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f164])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | ~spl2_2),
% 0.21/0.44    inference(superposition,[],[f22,f158])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    k1_xboole_0 = k1_tarski(sK1) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f156])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    spl2_2 <=> k1_xboole_0 = k1_tarski(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    spl2_1 | spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f148,f156,f152])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f139])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.44    inference(superposition,[],[f13,f117])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) | k1_tarski(X1) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.21/0.44    inference(forward_demodulation,[],[f96,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1))) | k1_tarski(X1) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.21/0.44    inference(superposition,[],[f25,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_tarski(X0) = k1_xboole_0) )),
% 0.21/0.44    inference(superposition,[],[f18,f14])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (2681)------------------------------
% 0.21/0.44  % (2681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (2681)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (2681)Memory used [KB]: 6268
% 0.21/0.44  % (2681)Time elapsed: 0.010 s
% 0.21/0.44  % (2681)------------------------------
% 0.21/0.44  % (2681)------------------------------
% 0.21/0.45  % (2664)Success in time 0.085 s
%------------------------------------------------------------------------------
