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
% DateTime   : Thu Dec  3 12:59:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  72 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  93 expanded)
%              Number of equality atoms :   34 (  69 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f40,f46])).

fof(f46,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3))
    | ~ spl4_1
    | spl4_3 ),
    inference(forward_demodulation,[],[f43,f30])).

fof(f30,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl4_1
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f43,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3))
    | ~ spl4_1
    | spl4_3 ),
    inference(forward_demodulation,[],[f41,f30])).

fof(f41,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) != k2_zfmisc_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)),k1_enumset1(sK3,sK3,sK3))
    | ~ spl4_1
    | spl4_3 ),
    inference(superposition,[],[f39,f30])).

fof(f39,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) != k1_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl4_3
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) = k1_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f40,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f25,f37])).

fof(f25,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) != k1_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f13,f24,f22,f22,f22,f22,f22,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f21,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f20,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f13,plain,(
    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3))
   => k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_mcart_1)).

fof(f31,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f26,f29])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f19,f15,f22,f15])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (13131)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.44  % (13128)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (13128)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f31,f40,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ~spl4_1 | spl4_3),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    $false | (~spl4_1 | spl4_3)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) | (~spl4_1 | spl4_3)),
% 0.21/0.44    inference(forward_demodulation,[],[f43,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) ) | ~spl4_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    spl4_1 <=> ! [X1,X0,X2] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) | (~spl4_1 | spl4_3)),
% 0.21/0.44    inference(forward_demodulation,[],[f41,f30])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) != k2_zfmisc_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)),k1_enumset1(sK3,sK3,sK3)) | (~spl4_1 | spl4_3)),
% 0.21/0.44    inference(superposition,[],[f39,f30])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) != k1_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) | spl4_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl4_3 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) = k1_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ~spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f37])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)) != k1_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),
% 0.21/0.44    inference(definition_unfolding,[],[f13,f24,f22,f22,f22,f22,f22,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f21,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f14,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f20,f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3)) => k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_mcart_1)).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl4_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f29])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f19,f15,f22,f15])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (13128)------------------------------
% 0.21/0.44  % (13128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (13128)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (13128)Memory used [KB]: 6140
% 0.21/0.44  % (13128)Time elapsed: 0.033 s
% 0.21/0.44  % (13128)------------------------------
% 0.21/0.44  % (13128)------------------------------
% 0.21/0.44  % (13120)Success in time 0.085 s
%------------------------------------------------------------------------------
