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
% DateTime   : Thu Dec  3 12:59:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 466 expanded)
%              Number of leaves         :   19 ( 159 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 ( 521 expanded)
%              Number of equality atoms :   78 ( 480 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f97,f106,f108,f118,f127])).

fof(f127,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_2 ),
    inference(superposition,[],[f70,f59])).

fof(f59,plain,
    ( k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_2
  <=> k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[],[f43,f42])).

fof(f42,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f23,f39,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f38])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f118,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_5 ),
    inference(superposition,[],[f70,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_5
  <=> k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f108,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f107,f61,f57,f53])).

fof(f53,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f61,plain,
    ( spl3_3
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f107,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f48,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f48,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f46,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f31,f38,f40,f38])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f46,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k5_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(backward_demodulation,[],[f41,f44])).

fof(f41,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k5_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f20,f40,f40,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f20,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

fof(f106,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f102])).

fof(f102,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_4 ),
    inference(superposition,[],[f70,f82])).

fof(f82,plain,
    ( k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_4
  <=> k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f97,plain,
    ( spl3_4
    | spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f95,f61,f84,f80])).

fof(f95,plain,
    ( k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_3 ),
    inference(superposition,[],[f63,f26])).

fof(f63,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f94,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_1 ),
    inference(superposition,[],[f71,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f71,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(superposition,[],[f70,f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:34:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (24502)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (24503)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (24502)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f128,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f94,f97,f106,f108,f118,f127])).
% 0.22/0.46  fof(f127,plain,(
% 0.22/0.46    ~spl3_2),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f126])).
% 0.22/0.46  fof(f126,plain,(
% 0.22/0.46    $false | ~spl3_2),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f123])).
% 0.22/0.46  fof(f123,plain,(
% 0.22/0.46    k1_xboole_0 != k1_xboole_0 | ~spl3_2),
% 0.22/0.46    inference(superposition,[],[f70,f59])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl3_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f57])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    spl3_2 <=> k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.46  fof(f70,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 != k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.46    inference(superposition,[],[f43,f42])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.22/0.46    inference(definition_unfolding,[],[f22,f39])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f24,f38])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f25,f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f29,f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f32,f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f33,f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.46    inference(rectify,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f23,f39,f40])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f21,f38])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,axiom,(
% 0.22/0.46    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.46  fof(f118,plain,(
% 0.22/0.46    ~spl3_5),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f117])).
% 0.22/0.46  fof(f117,plain,(
% 0.22/0.46    $false | ~spl3_5),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f114])).
% 0.22/0.46  fof(f114,plain,(
% 0.22/0.46    k1_xboole_0 != k1_xboole_0 | ~spl3_5),
% 0.22/0.46    inference(superposition,[],[f70,f86])).
% 0.22/0.46  fof(f86,plain,(
% 0.22/0.46    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl3_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f84])).
% 0.22/0.46  fof(f84,plain,(
% 0.22/0.46    spl3_5 <=> k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.46  fof(f108,plain,(
% 0.22/0.46    spl3_1 | spl3_2 | ~spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f107,f61,f57,f53])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    spl3_1 <=> k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    spl3_3 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.46  fof(f107,plain,(
% 0.22/0.46    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | k1_xboole_0 = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.46    inference(superposition,[],[f48,f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.46    inference(ennf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,axiom,(
% 0.22/0.46    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 0.22/0.46    inference(forward_demodulation,[],[f46,f44])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f31,f38,f40,f38])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k5_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 0.22/0.46    inference(backward_demodulation,[],[f41,f44])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k5_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 0.22/0.46    inference(definition_unfolding,[],[f20,f40,f40,f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.22/0.46    inference(ennf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.22/0.46    inference(negated_conjecture,[],[f13])).
% 0.22/0.46  fof(f13,conjecture,(
% 0.22/0.46    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).
% 0.22/0.46  fof(f106,plain,(
% 0.22/0.46    ~spl3_4),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f105])).
% 0.22/0.46  fof(f105,plain,(
% 0.22/0.46    $false | ~spl3_4),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f102])).
% 0.22/0.46  fof(f102,plain,(
% 0.22/0.46    k1_xboole_0 != k1_xboole_0 | ~spl3_4),
% 0.22/0.46    inference(superposition,[],[f70,f82])).
% 0.22/0.46  fof(f82,plain,(
% 0.22/0.46    k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f80])).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    spl3_4 <=> k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    spl3_4 | spl3_5 | spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f95,f61,f84,f80])).
% 0.22/0.46  fof(f95,plain,(
% 0.22/0.46    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_3),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f77])).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_3),
% 0.22/0.46    inference(superposition,[],[f63,f26])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | spl3_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f61])).
% 0.22/0.46  fof(f94,plain,(
% 0.22/0.46    ~spl3_1),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    $false | ~spl3_1),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f89])).
% 0.22/0.46  fof(f89,plain,(
% 0.22/0.46    k1_xboole_0 != k1_xboole_0 | ~spl3_1),
% 0.22/0.46    inference(superposition,[],[f71,f55])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    k1_xboole_0 = k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl3_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f53])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) )),
% 0.22/0.46    inference(superposition,[],[f70,f44])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (24502)------------------------------
% 0.22/0.46  % (24502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (24502)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (24502)Memory used [KB]: 6140
% 0.22/0.46  % (24502)Time elapsed: 0.048 s
% 0.22/0.46  % (24502)------------------------------
% 0.22/0.46  % (24502)------------------------------
% 0.22/0.47  % (24497)Success in time 0.104 s
%------------------------------------------------------------------------------
