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
% DateTime   : Thu Dec  3 12:46:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 149 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 ( 164 expanded)
%              Number of equality atoms :   48 ( 156 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f103])).

fof(f103,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f34,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(forward_demodulation,[],[f50,f27])).

fof(f27,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f16,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f50,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))) ),
    inference(superposition,[],[f45,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f20,f24,f25,f25])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) ),
    inference(unit_resulting_resolution,[],[f36,f36,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(superposition,[],[f30,f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f36,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f34,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f26,f32])).

fof(f26,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f15,f21,f24])).

fof(f15,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:40:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (1899)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (1899)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f35,f103])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl2_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    $false | spl2_1),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f34,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f50,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f16,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f17,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f19,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))))) )),
% 0.21/0.46    inference(superposition,[],[f45,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f20,f24,f25,f25])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_setfam_1(k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))))) )),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f36,f36,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.46    inference(superposition,[],[f30,f27])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f22,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.46    inference(superposition,[],[f28,f29])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f18,f25])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) | spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl2_1 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ~spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f32])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.46    inference(definition_unfolding,[],[f15,f21,f24])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    inference(negated_conjecture,[],[f9])).
% 0.21/0.46  fof(f9,conjecture,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (1899)------------------------------
% 0.21/0.46  % (1899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (1899)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (1899)Memory used [KB]: 6140
% 0.21/0.46  % (1899)Time elapsed: 0.044 s
% 0.21/0.46  % (1899)------------------------------
% 0.21/0.46  % (1899)------------------------------
% 0.21/0.46  % (1901)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (1890)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (1896)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (1895)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (1897)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (1886)Success in time 0.116 s
%------------------------------------------------------------------------------
