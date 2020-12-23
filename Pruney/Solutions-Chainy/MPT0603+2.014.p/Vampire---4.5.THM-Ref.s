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
% DateTime   : Thu Dec  3 12:51:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  82 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 209 expanded)
%              Number of equality atoms :   37 (  61 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f34,f38,f46,f50,f56,f62,f69,f78])).

fof(f78,plain,
    ( spl3_1
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl3_1
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f76,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_8
  <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f76,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0)
    | spl3_1
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f71,f61])).

fof(f61,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_9
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f71,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f23,f68])).

fof(f68,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_10
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f23,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f69,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f65,f48,f31,f67])).

fof(f31,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f65,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f49,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f62,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f57,f44,f26,f59])).

fof(f26,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f44,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f57,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f56,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f51,f36,f31,f53])).

fof(f36,plain,
    ( spl3_4
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f50,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f46,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f38,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f31])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f29,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f21])).

fof(f15,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:06:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (19814)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.46  % (19813)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.46  % (19813)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f24,f29,f34,f38,f46,f50,f56,f62,f69,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl3_1 | ~spl3_8 | ~spl3_9 | ~spl3_10),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    $false | (spl3_1 | ~spl3_8 | ~spl3_9 | ~spl3_10)),
% 0.21/0.46    inference(subsumption_resolution,[],[f76,f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) | ~spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl3_8 <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0) | (spl3_1 | ~spl3_9 | ~spl3_10)),
% 0.21/0.46    inference(forward_demodulation,[],[f71,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl3_9 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    k1_xboole_0 != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_10)),
% 0.21/0.46    inference(superposition,[],[f23,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl3_10 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    spl3_1 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl3_10 | ~spl3_3 | ~spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f65,f48,f31,f67])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl3_7 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | (~spl3_3 | ~spl3_7)),
% 0.21/0.46    inference(resolution,[],[f49,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f31])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) ) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl3_9 | ~spl3_2 | ~spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f57,f44,f26,f59])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    spl3_2 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl3_6 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_6)),
% 0.21/0.46    inference(resolution,[],[f45,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK1) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f26])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl3_8 | ~spl3_3 | ~spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f51,f36,f31,f53])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    spl3_4 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) | (~spl3_3 | ~spl3_4)),
% 0.21/0.46    inference(resolution,[],[f37,f33])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) ) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f36])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f48])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f44])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f36])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f13,f31])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.46    inference(negated_conjecture,[],[f4])).
% 0.21/0.46  fof(f4,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f14,f26])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f15,f21])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (19813)------------------------------
% 0.21/0.46  % (19813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (19813)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (19813)Memory used [KB]: 10490
% 0.21/0.46  % (19813)Time elapsed: 0.008 s
% 0.21/0.46  % (19813)------------------------------
% 0.21/0.46  % (19813)------------------------------
% 0.21/0.47  % (19807)Success in time 0.107 s
%------------------------------------------------------------------------------
