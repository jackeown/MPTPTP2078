%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  53 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 125 expanded)
%              Number of equality atoms :   23 (  63 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f31,f38,f48])).

fof(f48,plain,
    ( ~ spl2_1
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | ~ spl2_1
    | spl2_3 ),
    inference(subsumption_resolution,[],[f45,f30])).

fof(f30,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_3
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f45,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl2_1 ),
    inference(superposition,[],[f14,f20])).

fof(f20,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl2_1
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f14,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f38,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f37])).

fof(f37,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f35,f15])).

fof(f15,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f35,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f32,f24])).

fof(f24,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f32,plain,(
    ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(global_subsumption,[],[f16,f9,f8])).

fof(f8,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f9,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f10,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,
    ( ~ spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f26,f18,f28])).

fof(f26,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,sK0) ),
    inference(inner_rewriting,[],[f9])).

fof(f25,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f16,f22,f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:23:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (17039)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.47  % (17023)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.47  % (17023)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f25,f31,f38,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~spl2_1 | spl2_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    $false | (~spl2_1 | spl2_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f45,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK0) | spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    spl2_3 <=> r1_tarski(sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    r1_tarski(sK0,sK0) | ~spl2_1),
% 0.21/0.47    inference(superposition,[],[f14,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    sK0 = k1_tarski(sK1) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    spl2_1 <=> sK0 = k1_tarski(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~spl2_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    $false | ~spl2_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f35,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~r1_tarski(k1_xboole_0,k1_tarski(sK1)) | ~spl2_2),
% 0.21/0.47    inference(superposition,[],[f32,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    spl2_2 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.47    inference(global_subsumption,[],[f16,f9,f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f10,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ~spl2_3 | ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f18,f28])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,sK0)),
% 0.21/0.47    inference(inner_rewriting,[],[f9])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    spl2_1 | spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f16,f22,f18])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (17023)------------------------------
% 0.21/0.47  % (17023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17023)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (17023)Memory used [KB]: 10618
% 0.21/0.47  % (17023)Time elapsed: 0.062 s
% 0.21/0.47  % (17023)------------------------------
% 0.21/0.47  % (17023)------------------------------
% 0.21/0.47  % (17007)Success in time 0.117 s
%------------------------------------------------------------------------------
