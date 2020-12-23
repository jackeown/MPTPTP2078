%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  72 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 101 expanded)
%              Number of equality atoms :    9 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f48,f99])).

fof(f99,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f57,f59])).

fof(f59,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | spl2_2 ),
    inference(resolution,[],[f44,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f44,plain,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_2
  <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(forward_demodulation,[],[f53,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,X1)) ),
    inference(superposition,[],[f27,f30])).

fof(f27,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f22,f20,f20])).

fof(f22,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f48,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f46,f17])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f46,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | spl2_1 ),
    inference(resolution,[],[f40,f21])).

fof(f40,plain,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_1
  <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f45,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f34,f42,f38])).

fof(f34,plain,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1))
    | ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0)) ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
    ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) ),
    inference(definition_unfolding,[],[f16,f20,f20])).

fof(f16,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))
   => ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (17001)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (16997)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (16999)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (17009)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (16998)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (16997)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f45,f48,f99])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    spl2_2),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f94])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    $false | spl2_2),
% 0.22/0.47    inference(resolution,[],[f57,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | spl2_2),
% 0.22/0.47    inference(resolution,[],[f44,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1)) | spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl2_2 <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f53,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.47    inference(superposition,[],[f25,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f19,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f18,f20])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X1,X1))) )),
% 0.22/0.47    inference(superposition,[],[f27,f30])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f22,f20,f20])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl2_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    $false | spl2_1),
% 0.22/0.47    inference(resolution,[],[f46,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | spl2_1),
% 0.22/0.47    inference(resolution,[],[f40,f21])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0)) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl2_1 <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ~spl2_1 | ~spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f34,f42,f38])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1)) | ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0))),
% 0.22/0.47    inference(resolution,[],[f28,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))),
% 0.22/0.47    inference(definition_unfolding,[],[f16,f20,f20])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) => ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f8])).
% 0.22/0.47  fof(f8,conjecture,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f23,f20])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (16997)------------------------------
% 0.22/0.47  % (16997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (16997)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (16997)Memory used [KB]: 6140
% 0.22/0.47  % (16997)Time elapsed: 0.053 s
% 0.22/0.47  % (16997)------------------------------
% 0.22/0.47  % (16997)------------------------------
% 0.22/0.48  % (16996)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (16990)Success in time 0.111 s
%------------------------------------------------------------------------------
