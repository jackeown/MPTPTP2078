%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:56 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 126 expanded)
%              Number of leaves         :   14 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 181 expanded)
%              Number of equality atoms :   50 ( 115 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f106,f119,f134,f136,f149])).

fof(f149,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl3_2 ),
    inference(resolution,[],[f141,f17])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f141,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f30,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k1_enumset1(sK2,sK2,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_2
  <=> k1_xboole_0 = k1_enumset1(sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f30,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f136,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f135,f55,f51,f47])).

fof(f47,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f55,plain,
    ( spl3_3
  <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f135,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))
    | k1_xboole_0 = k1_enumset1(sK2,sK2,sK2)
    | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(superposition,[],[f39,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f39,plain,(
    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f35,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f27,f20,f28,f20])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f35,plain,(
    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k1_enumset1(sK2,sK2,sK2)))) ),
    inference(backward_demodulation,[],[f29,f33])).

fof(f29,plain,(
    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f16,f28,f28,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f16,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

fof(f134,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl3_5 ),
    inference(resolution,[],[f126,f17])).

fof(f126,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f30,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_5
  <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl3_4 ),
    inference(resolution,[],[f110,f17])).

fof(f110,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f30,f76])).

fof(f76,plain,
    ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_4
  <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f106,plain,
    ( spl3_4
    | spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f104,f55,f78,f74])).

fof(f104,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | spl3_3 ),
    inference(superposition,[],[f57,f23])).

fof(f57,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f103,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl3_1 ),
    inference(resolution,[],[f84,f17])).

fof(f84,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f36,f49])).

fof(f49,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f36,plain,(
    ! [X2,X0,X1] : ~ v1_xboole_0(k2_zfmisc_1(k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X1))) ),
    inference(superposition,[],[f30,f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (1217658885)
% 0.13/0.37  ipcrm: permission denied for id (1217691657)
% 0.13/0.37  ipcrm: permission denied for id (1217724428)
% 0.21/0.49  ipcrm: permission denied for id (1217790064)
% 0.37/0.58  % (10158)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.37/0.58  % (10152)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.37/0.58  % (10152)Refutation not found, incomplete strategy% (10152)------------------------------
% 0.37/0.58  % (10152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.58  % (10152)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.58  
% 0.37/0.58  % (10152)Memory used [KB]: 10490
% 0.37/0.58  % (10152)Time elapsed: 0.004 s
% 0.37/0.58  % (10152)------------------------------
% 0.37/0.58  % (10152)------------------------------
% 0.37/0.60  % (10150)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.37/0.61  % (10143)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.37/0.61  % (10149)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.37/0.62  % (10145)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.37/0.62  % (10141)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.37/0.62  % (10156)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.37/0.62  % (10145)Refutation found. Thanks to Tanya!
% 0.37/0.62  % SZS status Theorem for theBenchmark
% 0.37/0.62  % SZS output start Proof for theBenchmark
% 0.37/0.62  fof(f150,plain,(
% 0.37/0.62    $false),
% 0.37/0.62    inference(avatar_sat_refutation,[],[f103,f106,f119,f134,f136,f149])).
% 0.37/0.62  fof(f149,plain,(
% 0.37/0.62    ~spl3_2),
% 0.37/0.62    inference(avatar_contradiction_clause,[],[f148])).
% 0.37/0.62  fof(f148,plain,(
% 0.37/0.62    $false | ~spl3_2),
% 0.37/0.62    inference(resolution,[],[f141,f17])).
% 0.37/0.62  fof(f17,plain,(
% 0.37/0.62    v1_xboole_0(k1_xboole_0)),
% 0.37/0.62    inference(cnf_transformation,[],[f1])).
% 0.37/0.62  fof(f1,axiom,(
% 0.37/0.62    v1_xboole_0(k1_xboole_0)),
% 0.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.37/0.62  fof(f141,plain,(
% 0.37/0.62    ~v1_xboole_0(k1_xboole_0) | ~spl3_2),
% 0.37/0.62    inference(superposition,[],[f30,f53])).
% 0.37/0.62  fof(f53,plain,(
% 0.37/0.62    k1_xboole_0 = k1_enumset1(sK2,sK2,sK2) | ~spl3_2),
% 0.37/0.62    inference(avatar_component_clause,[],[f51])).
% 0.37/0.62  fof(f51,plain,(
% 0.37/0.62    spl3_2 <=> k1_xboole_0 = k1_enumset1(sK2,sK2,sK2)),
% 0.37/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.37/0.62  fof(f30,plain,(
% 0.37/0.62    ( ! [X0,X1] : (~v1_xboole_0(k1_enumset1(X0,X0,X1))) )),
% 0.37/0.62    inference(definition_unfolding,[],[f19,f20])).
% 0.37/0.62  fof(f20,plain,(
% 0.37/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.37/0.62    inference(cnf_transformation,[],[f3])).
% 0.37/0.62  fof(f3,axiom,(
% 0.37/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.37/0.62  fof(f19,plain,(
% 0.37/0.62    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.37/0.62    inference(cnf_transformation,[],[f4])).
% 0.37/0.62  fof(f4,axiom,(
% 0.37/0.62    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.37/0.62  fof(f136,plain,(
% 0.37/0.62    spl3_1 | spl3_2 | ~spl3_3),
% 0.37/0.62    inference(avatar_split_clause,[],[f135,f55,f51,f47])).
% 0.37/0.62  fof(f47,plain,(
% 0.37/0.62    spl3_1 <=> k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.37/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.37/0.62  fof(f55,plain,(
% 0.37/0.62    spl3_3 <=> k1_enumset1(sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))),
% 0.37/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.37/0.62  fof(f135,plain,(
% 0.37/0.62    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) | k1_xboole_0 = k1_enumset1(sK2,sK2,sK2) | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.37/0.62    inference(superposition,[],[f39,f23])).
% 0.37/0.62  fof(f23,plain,(
% 0.37/0.62    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.37/0.62    inference(cnf_transformation,[],[f13])).
% 0.37/0.62  fof(f13,plain,(
% 0.37/0.62    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.37/0.62    inference(ennf_transformation,[],[f7])).
% 0.37/0.62  fof(f7,axiom,(
% 0.37/0.62    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.37/0.62  fof(f39,plain,(
% 0.37/0.62    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK2))))),
% 0.37/0.62    inference(forward_demodulation,[],[f35,f33])).
% 0.37/0.62  fof(f33,plain,(
% 0.37/0.62    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.37/0.62    inference(definition_unfolding,[],[f27,f20,f28,f20])).
% 0.37/0.62  fof(f28,plain,(
% 0.37/0.62    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.37/0.62    inference(definition_unfolding,[],[f18,f20])).
% 0.37/0.62  fof(f18,plain,(
% 0.37/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.37/0.62    inference(cnf_transformation,[],[f2])).
% 0.37/0.62  fof(f2,axiom,(
% 0.37/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.37/0.62  fof(f27,plain,(
% 0.37/0.62    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.37/0.62    inference(cnf_transformation,[],[f6])).
% 0.37/0.62  fof(f6,axiom,(
% 0.37/0.62    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.37/0.62  fof(f35,plain,(
% 0.37/0.62    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k1_enumset1(sK2,sK2,sK2))))),
% 0.37/0.62    inference(backward_demodulation,[],[f29,f33])).
% 0.37/0.62  fof(f29,plain,(
% 0.37/0.62    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 0.37/0.62    inference(definition_unfolding,[],[f16,f28,f28,f25])).
% 0.37/0.62  fof(f25,plain,(
% 0.37/0.62    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.37/0.62    inference(cnf_transformation,[],[f8])).
% 0.37/0.62  fof(f8,axiom,(
% 0.37/0.62    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.37/0.62  fof(f16,plain,(
% 0.37/0.62    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.37/0.62    inference(cnf_transformation,[],[f15])).
% 0.37/0.62  fof(f15,plain,(
% 0.37/0.62    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.37/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).
% 0.37/0.62  fof(f14,plain,(
% 0.37/0.62    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.37/0.62    introduced(choice_axiom,[])).
% 0.37/0.62  fof(f11,plain,(
% 0.37/0.62    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.37/0.62    inference(ennf_transformation,[],[f10])).
% 0.37/0.62  fof(f10,negated_conjecture,(
% 0.37/0.62    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.37/0.62    inference(negated_conjecture,[],[f9])).
% 0.37/0.62  fof(f9,conjecture,(
% 0.37/0.62    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.37/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
% 0.37/0.62  fof(f134,plain,(
% 0.37/0.62    ~spl3_5),
% 0.37/0.62    inference(avatar_contradiction_clause,[],[f133])).
% 0.37/0.62  fof(f133,plain,(
% 0.37/0.62    $false | ~spl3_5),
% 0.37/0.62    inference(resolution,[],[f126,f17])).
% 0.37/0.62  fof(f126,plain,(
% 0.37/0.62    ~v1_xboole_0(k1_xboole_0) | ~spl3_5),
% 0.37/0.62    inference(superposition,[],[f30,f80])).
% 0.37/0.62  fof(f80,plain,(
% 0.37/0.62    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~spl3_5),
% 0.37/0.62    inference(avatar_component_clause,[],[f78])).
% 0.37/0.62  fof(f78,plain,(
% 0.37/0.62    spl3_5 <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.37/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.37/0.62  fof(f119,plain,(
% 0.37/0.62    ~spl3_4),
% 0.37/0.62    inference(avatar_contradiction_clause,[],[f118])).
% 0.37/0.62  fof(f118,plain,(
% 0.37/0.62    $false | ~spl3_4),
% 0.37/0.62    inference(resolution,[],[f110,f17])).
% 0.37/0.62  fof(f110,plain,(
% 0.37/0.62    ~v1_xboole_0(k1_xboole_0) | ~spl3_4),
% 0.37/0.62    inference(superposition,[],[f30,f76])).
% 0.37/0.62  fof(f76,plain,(
% 0.37/0.62    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~spl3_4),
% 0.37/0.62    inference(avatar_component_clause,[],[f74])).
% 0.37/0.62  fof(f74,plain,(
% 0.37/0.62    spl3_4 <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 0.37/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.37/0.62  fof(f106,plain,(
% 0.37/0.62    spl3_4 | spl3_5 | spl3_3),
% 0.37/0.62    inference(avatar_split_clause,[],[f104,f55,f78,f74])).
% 0.37/0.62  fof(f104,plain,(
% 0.37/0.62    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | spl3_3),
% 0.37/0.62    inference(trivial_inequality_removal,[],[f71])).
% 0.37/0.62  fof(f71,plain,(
% 0.37/0.62    k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | spl3_3),
% 0.37/0.62    inference(superposition,[],[f57,f23])).
% 0.37/0.62  fof(f57,plain,(
% 0.37/0.62    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) | spl3_3),
% 0.37/0.62    inference(avatar_component_clause,[],[f55])).
% 0.37/0.62  fof(f103,plain,(
% 0.37/0.62    ~spl3_1),
% 0.37/0.62    inference(avatar_contradiction_clause,[],[f102])).
% 0.37/0.62  fof(f102,plain,(
% 0.37/0.62    $false | ~spl3_1),
% 0.37/0.62    inference(resolution,[],[f84,f17])).
% 0.37/0.62  fof(f84,plain,(
% 0.37/0.62    ~v1_xboole_0(k1_xboole_0) | ~spl3_1),
% 0.37/0.62    inference(superposition,[],[f36,f49])).
% 0.37/0.62  fof(f49,plain,(
% 0.37/0.62    k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) | ~spl3_1),
% 0.37/0.62    inference(avatar_component_clause,[],[f47])).
% 0.37/0.62  fof(f36,plain,(
% 0.37/0.62    ( ! [X2,X0,X1] : (~v1_xboole_0(k2_zfmisc_1(k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X1)))) )),
% 0.37/0.62    inference(superposition,[],[f30,f33])).
% 0.37/0.62  % SZS output end Proof for theBenchmark
% 0.37/0.62  % (10145)------------------------------
% 0.37/0.62  % (10145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.62  % (10145)Termination reason: Refutation
% 0.37/0.62  
% 0.37/0.62  % (10145)Memory used [KB]: 6140
% 0.37/0.62  % (10145)Time elapsed: 0.059 s
% 0.37/0.62  % (10145)------------------------------
% 0.37/0.62  % (10145)------------------------------
% 0.37/0.63  % (10007)Success in time 0.272 s
%------------------------------------------------------------------------------
