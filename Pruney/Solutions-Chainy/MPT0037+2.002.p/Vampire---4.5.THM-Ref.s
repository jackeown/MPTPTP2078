%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  82 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :  110 ( 172 expanded)
%              Number of equality atoms :   38 (  66 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f34,f38,f42,f48,f54,f62,f77,f140,f182])).

fof(f182,plain,
    ( spl3_9
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl3_9
    | ~ spl3_19 ),
    inference(trivial_inequality_removal,[],[f176])).

fof(f176,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_9
    | ~ spl3_19 ),
    inference(superposition,[],[f60,f139])).

fof(f139,plain,
    ( ! [X6] : k3_xboole_0(sK1,k2_xboole_0(sK0,X6)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X6))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_19
  <=> ! [X6] : k3_xboole_0(sK1,k2_xboole_0(sK0,X6)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f60,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_9
  <=> k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f140,plain,
    ( spl3_19
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f125,f74,f51,f138])).

fof(f51,plain,
    ( spl3_8
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f74,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f125,plain,
    ( ! [X6] : k3_xboole_0(sK1,k2_xboole_0(sK0,X6)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X6))
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(superposition,[],[f75,f53])).

fof(f53,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f51])).

fof(f75,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f77,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f64,f40,f32,f74])).

fof(f32,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f40,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f64,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X5))
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f41,f33])).

fof(f33,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f32])).

fof(f41,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f40])).

fof(f62,plain,
    ( ~ spl3_9
    | ~ spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f56,f45,f32,f58])).

fof(f45,plain,
    ( spl3_7
  <=> k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f56,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_4
    | spl3_7 ),
    inference(superposition,[],[f47,f33])).

fof(f47,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f45])).

fof(f54,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f49,f36,f23,f51])).

fof(f23,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f36,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f49,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f37,f25])).

fof(f25,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f36])).

fof(f48,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f43,f32,f18,f45])).

fof(f18,plain,
    ( spl3_1
  <=> k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) = k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f20,f33])).

fof(f20,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f42,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f16,f40])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f38,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f15,f36])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f32])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f11,f23])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_xboole_1)).

fof(f21,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f18])).

fof(f12,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:50:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (1390)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.43  % (1393)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.44  % (1388)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.44  % (1388)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f183,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f21,f26,f34,f38,f42,f48,f54,f62,f77,f140,f182])).
% 0.20/0.44  fof(f182,plain,(
% 0.20/0.44    spl3_9 | ~spl3_19),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f181])).
% 0.20/0.44  fof(f181,plain,(
% 0.20/0.44    $false | (spl3_9 | ~spl3_19)),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f176])).
% 0.20/0.44  fof(f176,plain,(
% 0.20/0.44    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | (spl3_9 | ~spl3_19)),
% 0.20/0.44    inference(superposition,[],[f60,f139])).
% 0.20/0.44  fof(f139,plain,(
% 0.20/0.44    ( ! [X6] : (k3_xboole_0(sK1,k2_xboole_0(sK0,X6)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X6))) ) | ~spl3_19),
% 0.20/0.44    inference(avatar_component_clause,[],[f138])).
% 0.20/0.44  fof(f138,plain,(
% 0.20/0.44    spl3_19 <=> ! [X6] : k3_xboole_0(sK1,k2_xboole_0(sK0,X6)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X6))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl3_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f58])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    spl3_9 <=> k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.44  fof(f140,plain,(
% 0.20/0.44    spl3_19 | ~spl3_8 | ~spl3_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f125,f74,f51,f138])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    spl3_8 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    spl3_10 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.44  fof(f125,plain,(
% 0.20/0.44    ( ! [X6] : (k3_xboole_0(sK1,k2_xboole_0(sK0,X6)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X6))) ) | (~spl3_8 | ~spl3_10)),
% 0.20/0.44    inference(superposition,[],[f75,f53])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f51])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) ) | ~spl3_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f74])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    spl3_10 | ~spl3_4 | ~spl3_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f64,f40,f32,f74])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    spl3_6 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X5))) ) | (~spl3_4 | ~spl3_6)),
% 0.20/0.44    inference(superposition,[],[f41,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f32])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl3_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f40])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    ~spl3_9 | ~spl3_4 | spl3_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f56,f45,f32,f58])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    spl3_7 <=> k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_4 | spl3_7)),
% 0.20/0.44    inference(superposition,[],[f47,f33])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl3_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f45])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    spl3_8 | ~spl3_2 | ~spl3_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f49,f36,f23,f51])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    spl3_5 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    sK0 = k3_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_5)),
% 0.20/0.44    inference(resolution,[],[f37,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f23])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f36])).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    ~spl3_7 | spl3_1 | ~spl3_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f43,f32,f18,f45])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    spl3_1 <=> k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) = k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | (spl3_1 | ~spl3_4)),
% 0.20/0.44    inference(forward_demodulation,[],[f20,f33])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl3_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f18])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    spl3_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f16,f40])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    spl3_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f15,f36])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    spl3_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f14,f32])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    spl3_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f11,f23])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    r1_tarski(sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.44    inference(negated_conjecture,[],[f5])).
% 0.20/0.44  fof(f5,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_xboole_1)).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ~spl3_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f12,f18])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (1388)------------------------------
% 0.20/0.44  % (1388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (1388)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (1388)Memory used [KB]: 10618
% 0.20/0.44  % (1388)Time elapsed: 0.008 s
% 0.20/0.44  % (1388)------------------------------
% 0.20/0.44  % (1388)------------------------------
% 0.20/0.44  % (1385)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.44  % (1378)Success in time 0.082 s
%------------------------------------------------------------------------------
