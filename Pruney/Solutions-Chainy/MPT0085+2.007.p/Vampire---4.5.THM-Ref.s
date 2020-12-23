%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  72 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :  104 ( 150 expanded)
%              Number of equality atoms :   38 (  58 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f31,f35,f43,f47,f58,f68,f81,f103])).

fof(f103,plain,
    ( spl3_1
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl3_1
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2)
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f21,f80])).

% (26616)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f80,plain,
    ( ! [X0] : k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_10
  <=> ! [X0] : k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f21,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl3_1
  <=> k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f81,plain,
    ( spl3_10
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f77,f65,f53,f45,f79])).

fof(f45,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f53,plain,
    ( spl3_8
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f65,plain,
    ( spl3_9
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f77,plain,
    ( ! [X0] : k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f71,f54])).

fof(f54,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f71,plain,
    ( ! [X0] : k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f46,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f46,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f45])).

fof(f68,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f63,f41,f24,f65])).

fof(f24,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f41,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f63,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f42,f26])).

fof(f26,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f41])).

fof(f58,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f51,f33,f29,f53])).

fof(f29,plain,
    ( spl3_3
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f33,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f30,f34])).

fof(f34,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f30,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f47,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f17,f45])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f43,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f15,f41])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f35,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f31,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f27,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f11,f24])).

fof(f11,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f22,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f19])).

fof(f12,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:56:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (26617)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (26621)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.45  % (26618)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.45  % (26617)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f22,f27,f31,f35,f43,f47,f58,f68,f81,f103])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    spl3_1 | ~spl3_10),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    $false | (spl3_1 | ~spl3_10)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f98])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2) | (spl3_1 | ~spl3_10)),
% 0.21/0.45    inference(superposition,[],[f21,f80])).
% 0.21/0.45  % (26616)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X0] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) ) | ~spl3_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    spl3_10 <=> ! [X0] : k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    spl3_1 <=> k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl3_10 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f77,f65,f53,f45,f79])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    spl3_7 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl3_8 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl3_9 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    ( ! [X0] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) ) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.21/0.45    inference(forward_demodulation,[],[f71,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl3_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f53])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X0] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ) | (~spl3_7 | ~spl3_9)),
% 0.21/0.45    inference(superposition,[],[f46,f67])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f65])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f45])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    spl3_9 | ~spl3_2 | ~spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f63,f41,f24,f65])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    spl3_2 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    spl3_6 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_6)),
% 0.21/0.45    inference(resolution,[],[f42,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f24])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f41])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl3_8 | ~spl3_3 | ~spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f51,f33,f29,f53])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    spl3_3 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    spl3_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_3 | ~spl3_4)),
% 0.21/0.45    inference(superposition,[],[f30,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f33])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f29])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f17,f45])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f15,f41])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f14,f33])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f13,f29])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f11,f24])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.45    inference(negated_conjecture,[],[f5])).
% 0.21/0.45  fof(f5,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f12,f19])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (26617)------------------------------
% 0.21/0.45  % (26617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (26617)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (26617)Memory used [KB]: 10618
% 0.21/0.45  % (26617)Time elapsed: 0.005 s
% 0.21/0.45  % (26617)------------------------------
% 0.21/0.45  % (26617)------------------------------
% 0.21/0.45  % (26611)Success in time 0.083 s
%------------------------------------------------------------------------------
