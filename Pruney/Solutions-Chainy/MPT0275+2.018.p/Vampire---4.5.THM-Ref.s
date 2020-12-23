%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  64 expanded)
%              Number of leaves         :    6 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 152 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f28,f39,f44,f59])).

fof(f59,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f57,f16])).

fof(f16,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl3_1
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f47,f21])).

fof(f21,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f47,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,sK2)
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X8,sK1),sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f34,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ r2_hidden(X8,X7)
      | k1_xboole_0 = k4_xboole_0(k2_tarski(X8,X6),X7) ) ),
    inference(resolution,[],[f13,f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f44,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f43])).

fof(f43,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_1
    | spl3_2 ),
    inference(superposition,[],[f41,f17])).

fof(f17,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f41,plain,
    ( ! [X1] : k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,X1),sK2)
    | spl3_2 ),
    inference(resolution,[],[f20,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(resolution,[],[f11,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f20,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f39,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f38])).

fof(f38,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f37])).

fof(f37,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_1
    | spl3_3 ),
    inference(superposition,[],[f36,f17])).

fof(f36,plain,
    ( ! [X0] : k1_xboole_0 != k4_xboole_0(k2_tarski(X0,sK1),sK2)
    | spl3_3 ),
    inference(resolution,[],[f31,f25])).

fof(f25,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f24])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X2,X0),X1) ) ),
    inference(resolution,[],[f12,f10])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f6,f19,f24,f15])).

fof(f6,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f27,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f8,f24,f15])).

fof(f8,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f22,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f7,f19,f15])).

fof(f7,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (11121)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (11114)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.43  % (11122)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.43  % (11123)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (11114)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f22,f27,f28,f39,f44,f59])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f58])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    $false | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.20/0.44    inference(subsumption_resolution,[],[f57,f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | spl3_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    spl3_1 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | (~spl3_2 | ~spl3_3)),
% 0.20/0.44    inference(resolution,[],[f47,f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    r2_hidden(sK0,sK2) | ~spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    spl3_2 <=> r2_hidden(sK0,sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ( ! [X8] : (~r2_hidden(X8,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(X8,sK1),sK2)) ) | ~spl3_3),
% 0.20/0.44    inference(resolution,[],[f34,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    r2_hidden(sK1,sK2) | ~spl3_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    spl3_3 <=> r2_hidden(sK1,sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X6,X8,X7] : (~r2_hidden(X6,X7) | ~r2_hidden(X8,X7) | k1_xboole_0 = k4_xboole_0(k2_tarski(X8,X6),X7)) )),
% 0.20/0.44    inference(resolution,[],[f13,f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    ~spl3_1 | spl3_2),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    $false | (~spl3_1 | spl3_2)),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    k1_xboole_0 != k1_xboole_0 | (~spl3_1 | spl3_2)),
% 0.20/0.44    inference(superposition,[],[f41,f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f15])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ( ! [X1] : (k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,X1),sK2)) ) | spl3_2),
% 0.20/0.44    inference(resolution,[],[f20,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X2),X1)) )),
% 0.20/0.44    inference(resolution,[],[f11,f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ~r2_hidden(sK0,sK2) | spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f19])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ~spl3_1 | spl3_3),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    $false | (~spl3_1 | spl3_3)),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    k1_xboole_0 != k1_xboole_0 | (~spl3_1 | spl3_3)),
% 0.20/0.44    inference(superposition,[],[f36,f17])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k2_tarski(X0,sK1),sK2)) ) | spl3_3),
% 0.20/0.44    inference(resolution,[],[f31,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ~r2_hidden(sK1,sK2) | spl3_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f24])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k2_tarski(X2,X0),X1)) )),
% 0.20/0.44    inference(resolution,[],[f12,f10])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ~spl3_1 | ~spl3_3 | ~spl3_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f6,f19,f24,f15])).
% 0.20/0.44  fof(f6,plain,(
% 0.20/0.44    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.44    inference(negated_conjecture,[],[f3])).
% 0.20/0.44  fof(f3,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    spl3_1 | spl3_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f8,f24,f15])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    spl3_1 | spl3_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f7,f19,f15])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (11114)------------------------------
% 0.20/0.44  % (11114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (11114)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (11114)Memory used [KB]: 10618
% 0.20/0.44  % (11114)Time elapsed: 0.006 s
% 0.20/0.44  % (11114)------------------------------
% 0.20/0.44  % (11114)------------------------------
% 0.20/0.44  % (11116)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.44  % (11111)Success in time 0.081 s
%------------------------------------------------------------------------------
