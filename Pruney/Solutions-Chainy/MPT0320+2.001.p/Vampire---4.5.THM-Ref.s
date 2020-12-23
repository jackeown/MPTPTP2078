%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  65 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  84 expanded)
%              Number of equality atoms :   41 (  74 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f36])).

fof(f36,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f35])).

fof(f35,plain,
    ( $false
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f34])).

fof(f34,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_zfmisc_1(k2_tarski(sK0,sK1),sK2)
    | spl3_1 ),
    inference(forward_demodulation,[],[f32,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f13,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) ),
    inference(definition_unfolding,[],[f15,f14,f12])).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_zfmisc_1(k3_tarski(k2_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),sK2)
    | spl3_1 ),
    inference(superposition,[],[f29,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f16,f14,f14])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f29,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_1
  <=> k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) = k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f30,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f27])).

fof(f25,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) ),
    inference(trivial_inequality_removal,[],[f24])).

fof(f24,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_zfmisc_1(sK2,k2_tarski(sK0,sK1))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) ),
    inference(forward_demodulation,[],[f23,f19])).

fof(f23,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_zfmisc_1(sK2,k3_tarski(k2_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) ),
    inference(backward_demodulation,[],[f20,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f17,f14,f14])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f20,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k3_tarski(k2_tarski(k2_zfmisc_1(sK2,k2_tarski(sK0,sK0)),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1))))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f11,f14,f12,f12,f14,f12,f12])).

fof(f11,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
      | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (15112)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.44  % (15112)Refutation not found, incomplete strategy% (15112)------------------------------
% 0.20/0.44  % (15112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (15112)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (15112)Memory used [KB]: 10618
% 0.20/0.44  % (15112)Time elapsed: 0.004 s
% 0.20/0.44  % (15112)------------------------------
% 0.20/0.44  % (15112)------------------------------
% 0.20/0.45  % (15116)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (15116)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f30,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    $false | spl3_1),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) | spl3_1),
% 0.20/0.46    inference(forward_demodulation,[],[f32,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f13,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f15,f14,f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_zfmisc_1(k3_tarski(k2_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),sK2) | spl3_1),
% 0.20/0.46    inference(superposition,[],[f29,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f16,f14,f14])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) | spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    spl3_1 <=> k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) = k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ~spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f27])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))),
% 0.20/0.46    inference(forward_demodulation,[],[f23,f19])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_zfmisc_1(sK2,k3_tarski(k2_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))),
% 0.20/0.46    inference(backward_demodulation,[],[f20,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f17,f14,f14])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k3_tarski(k2_tarski(k2_zfmisc_1(sK2,k2_tarski(sK0,sK0)),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1)))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(sK0,sK0),sK2),k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))),
% 0.20/0.46    inference(definition_unfolding,[],[f11,f14,f12,f12,f14,f12,f12])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2))) => (k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.20/0.46    inference(negated_conjecture,[],[f6])).
% 0.20/0.46  fof(f6,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (15116)------------------------------
% 0.20/0.46  % (15116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (15116)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (15116)Memory used [KB]: 10618
% 0.20/0.46  % (15116)Time elapsed: 0.004 s
% 0.20/0.46  % (15116)------------------------------
% 0.20/0.46  % (15116)------------------------------
% 0.20/0.46  % (15097)Success in time 0.102 s
%------------------------------------------------------------------------------
