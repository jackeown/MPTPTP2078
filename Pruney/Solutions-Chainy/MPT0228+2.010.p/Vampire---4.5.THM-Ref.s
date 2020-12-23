%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  37 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  71 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f44,f48])).

fof(f48,plain,
    ( spl2_1
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl2_1
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f32,f43,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f43,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_3
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f32,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f44,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f39,f35,f41])).

fof(f35,plain,
    ( spl2_2
  <=> k1_tarski(sK0) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f39,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_2 ),
    inference(superposition,[],[f37,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f37,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f38,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f27,f35])).

fof(f27,plain,(
    k1_tarski(sK0) != k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f18,plain,(
    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
        & X0 != X1 )
   => ( k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (26765)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (26769)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (26768)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (26764)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (26772)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (26774)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (26774)Refutation not found, incomplete strategy% (26774)------------------------------
% 0.22/0.53  % (26774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26774)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26774)Memory used [KB]: 10618
% 0.22/0.53  % (26774)Time elapsed: 0.108 s
% 0.22/0.53  % (26774)------------------------------
% 0.22/0.53  % (26774)------------------------------
% 0.22/0.53  % (26772)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f33,f38,f44,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    spl2_1 | spl2_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    $false | (spl2_1 | spl2_3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f32,f43,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    spl2_3 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    sK0 != sK1 | spl2_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    spl2_1 <=> sK0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ~spl2_3 | spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f35,f41])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    spl2_2 <=> k1_tarski(sK0) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_2),
% 0.22/0.53    inference(superposition,[],[f37,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    k1_tarski(sK0) != k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1)) | spl2_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f35])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ~spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f35])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    k1_tarski(sK0) != k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1))),
% 0.22/0.53    inference(definition_unfolding,[],[f18,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) & sK0 != sK1),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1) => (k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) & sK0 != sK1)),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1)),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ~spl2_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f17,f30])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    sK0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (26772)------------------------------
% 0.22/0.53  % (26772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26772)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (26772)Memory used [KB]: 10618
% 0.22/0.53  % (26772)Time elapsed: 0.108 s
% 0.22/0.53  % (26772)------------------------------
% 0.22/0.53  % (26772)------------------------------
% 0.22/0.54  % (26761)Success in time 0.168 s
%------------------------------------------------------------------------------
