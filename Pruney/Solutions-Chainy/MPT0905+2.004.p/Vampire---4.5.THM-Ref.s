%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:19 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 316 expanded)
%              Number of leaves         :   15 ( 109 expanded)
%              Depth                    :   14
%              Number of atoms          :   56 ( 324 expanded)
%              Number of equality atoms :   46 ( 313 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53])).

fof(f53,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f51])).

fof(f51,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | spl4_1 ),
    inference(forward_demodulation,[],[f50,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f22,f38,f38,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f50,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | spl4_1 ),
    inference(forward_demodulation,[],[f49,f42])).

fof(f49,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k2_zfmisc_1(k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | spl4_1 ),
    inference(superposition,[],[f47,f42])).

fof(f47,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k6_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f48,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f41,f45])).

fof(f41,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k6_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f19,f39,f38,f38,f38,f38,f38,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f19,plain,(
    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3))
   => k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n019.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 15:27:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.42  % (8743)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.18/0.42  % (8746)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.18/0.42  % (8746)Refutation found. Thanks to Tanya!
% 0.18/0.42  % SZS status Theorem for theBenchmark
% 0.18/0.42  % SZS output start Proof for theBenchmark
% 0.18/0.42  fof(f54,plain,(
% 0.18/0.42    $false),
% 0.18/0.42    inference(avatar_sat_refutation,[],[f48,f53])).
% 0.18/0.42  fof(f53,plain,(
% 0.18/0.42    spl4_1),
% 0.18/0.42    inference(avatar_contradiction_clause,[],[f52])).
% 0.18/0.42  fof(f52,plain,(
% 0.18/0.42    $false | spl4_1),
% 0.18/0.42    inference(trivial_inequality_removal,[],[f51])).
% 0.18/0.42  fof(f51,plain,(
% 0.18/0.42    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | spl4_1),
% 0.18/0.42    inference(forward_demodulation,[],[f50,f42])).
% 0.18/0.42  fof(f42,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) )),
% 0.18/0.42    inference(definition_unfolding,[],[f22,f38,f38,f38])).
% 0.18/0.42  fof(f38,plain,(
% 0.18/0.42    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.18/0.42    inference(definition_unfolding,[],[f20,f37])).
% 0.18/0.42  fof(f37,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.18/0.42    inference(definition_unfolding,[],[f21,f36])).
% 0.18/0.42  fof(f36,plain,(
% 0.18/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.18/0.42    inference(definition_unfolding,[],[f25,f35])).
% 0.18/0.42  fof(f35,plain,(
% 0.18/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.18/0.42    inference(definition_unfolding,[],[f29,f34])).
% 0.18/0.42  fof(f34,plain,(
% 0.18/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.18/0.42    inference(definition_unfolding,[],[f30,f33])).
% 0.18/0.42  fof(f33,plain,(
% 0.18/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.18/0.42    inference(definition_unfolding,[],[f31,f32])).
% 0.18/0.42  fof(f32,plain,(
% 0.18/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f7])).
% 0.18/0.42  fof(f7,axiom,(
% 0.18/0.42    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.18/0.42  fof(f31,plain,(
% 0.18/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f6])).
% 0.18/0.42  fof(f6,axiom,(
% 0.18/0.42    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.18/0.42  fof(f30,plain,(
% 0.18/0.42    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f5])).
% 0.18/0.42  fof(f5,axiom,(
% 0.18/0.42    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.18/0.42  fof(f29,plain,(
% 0.18/0.42    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f4])).
% 0.18/0.42  fof(f4,axiom,(
% 0.18/0.42    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.18/0.42  fof(f25,plain,(
% 0.18/0.42    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f3])).
% 0.18/0.42  fof(f3,axiom,(
% 0.18/0.42    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.42  fof(f21,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f2])).
% 0.18/0.42  fof(f2,axiom,(
% 0.18/0.42    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.42  fof(f20,plain,(
% 0.18/0.42    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f1])).
% 0.18/0.42  fof(f1,axiom,(
% 0.18/0.42    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.42  fof(f22,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 0.18/0.42    inference(cnf_transformation,[],[f8])).
% 0.18/0.42  fof(f8,axiom,(
% 0.18/0.42    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 0.18/0.42  fof(f50,plain,(
% 0.18/0.42    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | spl4_1),
% 0.18/0.42    inference(forward_demodulation,[],[f49,f42])).
% 0.18/0.42  fof(f49,plain,(
% 0.18/0.42    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k2_zfmisc_1(k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | spl4_1),
% 0.18/0.42    inference(superposition,[],[f47,f42])).
% 0.18/0.42  fof(f47,plain,(
% 0.18/0.42    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k6_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) | spl4_1),
% 0.18/0.42    inference(avatar_component_clause,[],[f45])).
% 0.18/0.43  fof(f45,plain,(
% 0.18/0.43    spl4_1 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.18/0.43  fof(f48,plain,(
% 0.18/0.43    ~spl4_1),
% 0.18/0.43    inference(avatar_split_clause,[],[f41,f45])).
% 0.18/0.43  fof(f41,plain,(
% 0.18/0.43    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k6_enumset1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),
% 0.18/0.43    inference(definition_unfolding,[],[f19,f39,f38,f38,f38,f38,f38,f40])).
% 0.18/0.43  fof(f40,plain,(
% 0.18/0.43    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.18/0.43    inference(definition_unfolding,[],[f28,f23])).
% 0.18/0.43  fof(f23,plain,(
% 0.18/0.43    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f9])).
% 0.18/0.43  fof(f9,axiom,(
% 0.18/0.43    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.18/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.18/0.43  fof(f28,plain,(
% 0.18/0.43    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f12])).
% 0.18/0.43  fof(f12,axiom,(
% 0.18/0.43    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.18/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).
% 0.18/0.43  fof(f39,plain,(
% 0.18/0.43    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.18/0.43    inference(definition_unfolding,[],[f27,f24])).
% 0.18/0.43  fof(f24,plain,(
% 0.18/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f10])).
% 0.18/0.43  fof(f10,axiom,(
% 0.18/0.43    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.18/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.18/0.43  fof(f27,plain,(
% 0.18/0.43    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f11])).
% 0.18/0.43  fof(f11,axiom,(
% 0.18/0.43    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.18/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.18/0.43  fof(f19,plain,(
% 0.18/0.43    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.18/0.43    inference(cnf_transformation,[],[f18])).
% 0.18/0.43  fof(f18,plain,(
% 0.18/0.43    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.18/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 0.18/0.43  fof(f17,plain,(
% 0.18/0.43    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3)) => k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.18/0.43    introduced(choice_axiom,[])).
% 0.18/0.43  fof(f16,plain,(
% 0.18/0.43    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.18/0.43    inference(ennf_transformation,[],[f15])).
% 0.18/0.43  fof(f15,negated_conjecture,(
% 0.18/0.43    ~! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.18/0.43    inference(negated_conjecture,[],[f14])).
% 0.18/0.43  fof(f14,conjecture,(
% 0.18/0.43    ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.18/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_mcart_1)).
% 0.18/0.43  % SZS output end Proof for theBenchmark
% 0.18/0.43  % (8746)------------------------------
% 0.18/0.43  % (8746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.43  % (8746)Termination reason: Refutation
% 0.18/0.43  
% 0.18/0.43  % (8746)Memory used [KB]: 10618
% 0.18/0.43  % (8746)Time elapsed: 0.006 s
% 0.18/0.43  % (8746)------------------------------
% 0.18/0.43  % (8746)------------------------------
% 0.18/0.43  % (8730)Success in time 0.093 s
%------------------------------------------------------------------------------
