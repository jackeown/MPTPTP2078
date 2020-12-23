%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  50 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  65 expanded)
%              Number of equality atoms :   24 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f38,f46])).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f23,f37])).

fof(f37,plain,
    ( k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k2_zfmisc_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)),k2_tarski(sK3,sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_2
  <=> k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) = k2_zfmisc_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)),k2_tarski(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X2)) ),
    inference(definition_unfolding,[],[f18,f14])).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f38,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f33,f28,f35])).

fof(f28,plain,
    ( spl4_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) = k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f33,plain,
    ( k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k2_zfmisc_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)),k2_tarski(sK3,sK3))
    | spl4_1 ),
    inference(forward_demodulation,[],[f32,f23])).

fof(f32,plain,
    ( k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3))
    | spl4_1 ),
    inference(forward_demodulation,[],[f30,f23])).

fof(f30,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f31,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f28])).

fof(f22,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f13,f19,f14,f14,f14,f14,f14,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (19252)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (19259)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (19259)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f31,f38,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    $false | spl4_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f23,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k2_zfmisc_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)),k2_tarski(sK3,sK3)) | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl4_2 <=> k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) = k2_zfmisc_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)),k2_tarski(sK3,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X2))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f18,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ~spl4_2 | spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f28,f35])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    spl4_1 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) = k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k2_zfmisc_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)),k2_tarski(sK3,sK3)) | spl4_1),
% 0.21/0.49    inference(forward_demodulation,[],[f32,f23])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) | spl4_1),
% 0.21/0.49    inference(forward_demodulation,[],[f30,f23])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f28])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f28])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != k2_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),
% 0.21/0.49    inference(definition_unfolding,[],[f13,f19,f14,f14,f14,f14,f14,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3)) => k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_mcart_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (19259)------------------------------
% 0.21/0.49  % (19259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19259)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (19259)Memory used [KB]: 10618
% 0.21/0.49  % (19259)Time elapsed: 0.080 s
% 0.21/0.49  % (19259)------------------------------
% 0.21/0.49  % (19259)------------------------------
% 0.21/0.49  % (19240)Success in time 0.137 s
%------------------------------------------------------------------------------
