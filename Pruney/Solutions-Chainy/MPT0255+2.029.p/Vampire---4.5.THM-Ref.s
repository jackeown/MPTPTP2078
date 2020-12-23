%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 114 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 148 expanded)
%              Number of equality atoms :   52 ( 116 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f49,f58,f95])).

fof(f95,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f90,f73])).

fof(f73,plain,(
    ! [X6,X4,X5,X3] : k1_xboole_0 != k2_enumset1(X3,X4,X5,X6) ),
    inference(subsumption_resolution,[],[f72,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_xboole_0 != k2_enumset1(X0,X0,X1,X2) ),
    inference(superposition,[],[f31,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) ),
    inference(definition_unfolding,[],[f26,f27,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f20,f27,f28])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f72,plain,(
    ! [X6,X4,X5,X3] :
      ( k1_xboole_0 != k2_enumset1(X3,X4,X5,X6)
      | k1_xboole_0 = k2_enumset1(X3,X3,X3,X4) ) ),
    inference(superposition,[],[f34,f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f90,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f57,f35])).

fof(f35,plain,(
    ! [X0] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f18,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f57,plain,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_3
  <=> k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f58,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f53,f46,f55])).

fof(f46,plain,
    ( spl3_2
  <=> k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f48,f50])).

fof(f50,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f48,f34])).

fof(f48,plain,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f49,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f44,f40,f46])).

fof(f40,plain,
    ( spl3_1
  <=> k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f42,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f21,f23,f23])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f42,plain,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f43,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f40])).

fof(f30,plain,(
    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f17,f27,f23])).

fof(f17,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:16:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (25624)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.45  % (25624)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f43,f49,f58,f95])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ~spl3_3),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    $false | ~spl3_3),
% 0.21/0.45    inference(subsumption_resolution,[],[f90,f73])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ( ! [X6,X4,X5,X3] : (k1_xboole_0 != k2_enumset1(X3,X4,X5,X6)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f72,f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.45    inference(superposition,[],[f31,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f26,f27,f23,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f22,f23])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f20,f27,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f19,f23])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X6,X4,X5,X3] : (k1_xboole_0 != k2_enumset1(X3,X4,X5,X6) | k1_xboole_0 = k2_enumset1(X3,X3,X3,X4)) )),
% 0.21/0.46    inference(superposition,[],[f34,f29])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f25,f27])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) | ~spl3_3),
% 0.21/0.46    inference(superposition,[],[f57,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0] : (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f18,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1) )),
% 0.21/0.46    inference(definition_unfolding,[],[f24,f27])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1))) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl3_3 <=> k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl3_3 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f53,f46,f55])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl3_2 <=> k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1))) | ~spl3_2),
% 0.21/0.46    inference(backward_demodulation,[],[f48,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    k1_xboole_0 = sK2 | ~spl3_2),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f34])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f46])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl3_2 | ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f44,f40,f46])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl3_1 <=> k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))) | ~spl3_1),
% 0.21/0.46    inference(forward_demodulation,[],[f42,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f21,f23,f23])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2)) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f40])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f40])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 0.21/0.46    inference(definition_unfolding,[],[f17,f27,f23])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.46    inference(negated_conjecture,[],[f10])).
% 0.21/0.46  fof(f10,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (25624)------------------------------
% 0.21/0.46  % (25624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (25624)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (25624)Memory used [KB]: 10618
% 0.21/0.46  % (25624)Time elapsed: 0.009 s
% 0.21/0.46  % (25624)------------------------------
% 0.21/0.46  % (25624)------------------------------
% 0.21/0.46  % (25607)Success in time 0.102 s
%------------------------------------------------------------------------------
