%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  82 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :  114 ( 160 expanded)
%              Number of equality atoms :   49 (  72 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f55,f64,f72,f82,f137,f146,f299,f311])).

fof(f311,plain,
    ( spl3_1
    | ~ spl3_16
    | ~ spl3_18
    | ~ spl3_30 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | spl3_1
    | ~ spl3_16
    | ~ spl3_18
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f34,f309])).

fof(f309,plain,
    ( ! [X2,X0,X1] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))
    | ~ spl3_16
    | ~ spl3_18
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f305,f145])).

fof(f145,plain,
    ( ! [X6,X4,X5] : k3_mcart_1(X4,X5,X6) = k4_tarski(k4_tarski(X4,X5),X6)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_18
  <=> ! [X5,X4,X6] : k3_mcart_1(X4,X5,X6) = k4_tarski(k4_tarski(X4,X5),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f305,plain,
    ( ! [X2,X0,X1] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(k4_tarski(X0,X1),X2))
    | ~ spl3_16
    | ~ spl3_30 ),
    inference(superposition,[],[f298,f136])).

fof(f136,plain,
    ( ! [X4,X3] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_16
  <=> ! [X3,X4] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f298,plain,
    ( ! [X2,X0,X1] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl3_30
  <=> ! [X1,X0,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f34,plain,
    ( k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f299,plain,
    ( spl3_30
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f138,f135,f53,f297])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f138,plain,
    ( ! [X2,X0,X1] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2)
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(superposition,[],[f54,f136])).

fof(f54,plain,
    ( ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f146,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f93,f70,f62,f41,f144])).

fof(f41,plain,
    ( spl3_3
  <=> ! [X1,X0] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( spl3_8
  <=> ! [X1,X3,X0,X2] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f70,plain,
    ( spl3_10
  <=> ! [X1,X3,X0,X2] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f93,plain,
    ( ! [X6,X4,X5] : k3_mcart_1(X4,X5,X6) = k4_tarski(k4_tarski(X4,X5),X6)
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f91,f74])).

fof(f74,plain,
    ( ! [X6,X4,X7,X5] : k3_mcart_1(X4,X5,X6) = k1_mcart_1(k4_mcart_1(X4,X5,X6,X7))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f42,f63])).

fof(f63,plain,
    ( ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f42,plain,
    ( ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f91,plain,
    ( ! [X6,X4,X7,X5] : k1_mcart_1(k4_mcart_1(X4,X5,X6,X7)) = k4_tarski(k4_tarski(X4,X5),X6)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f42,f71])).

fof(f71,plain,
    ( ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f137,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f110,f80,f37,f135])).

fof(f37,plain,
    ( spl3_2
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f80,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f110,plain,
    ( ! [X4,X3] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f102,f38])).

fof(f38,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f102,plain,
    ( ! [X4,X3] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X4))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(superposition,[],[f81,f38])).

fof(f81,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f24,f80])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f72,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f43,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f32])).

fof(f17,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2))
   => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:49:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (29749)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.42  % (29749)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.43  % (29755)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f313,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f35,f39,f43,f55,f64,f72,f82,f137,f146,f299,f311])).
% 0.21/0.43  fof(f311,plain,(
% 0.21/0.43    spl3_1 | ~spl3_16 | ~spl3_18 | ~spl3_30),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f310])).
% 0.21/0.43  fof(f310,plain,(
% 0.21/0.43    $false | (spl3_1 | ~spl3_16 | ~spl3_18 | ~spl3_30)),
% 0.21/0.43    inference(subsumption_resolution,[],[f34,f309])).
% 0.21/0.43  fof(f309,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))) ) | (~spl3_16 | ~spl3_18 | ~spl3_30)),
% 0.21/0.43    inference(forward_demodulation,[],[f305,f145])).
% 0.21/0.43  fof(f145,plain,(
% 0.21/0.43    ( ! [X6,X4,X5] : (k3_mcart_1(X4,X5,X6) = k4_tarski(k4_tarski(X4,X5),X6)) ) | ~spl3_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f144])).
% 0.21/0.43  fof(f144,plain,(
% 0.21/0.43    spl3_18 <=> ! [X5,X4,X6] : k3_mcart_1(X4,X5,X6) = k4_tarski(k4_tarski(X4,X5),X6)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.43  fof(f305,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(k4_tarski(X0,X1),X2))) ) | (~spl3_16 | ~spl3_30)),
% 0.21/0.43    inference(superposition,[],[f298,f136])).
% 0.21/0.43  fof(f136,plain,(
% 0.21/0.43    ( ! [X4,X3] : (k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4))) ) | ~spl3_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f135])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    spl3_16 <=> ! [X3,X4] : k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.43  fof(f298,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2)) ) | ~spl3_30),
% 0.21/0.43    inference(avatar_component_clause,[],[f297])).
% 0.21/0.43  fof(f297,plain,(
% 0.21/0.43    spl3_30 <=> ! [X1,X0,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl3_1 <=> k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f299,plain,(
% 0.21/0.43    spl3_30 | ~spl3_6 | ~spl3_16),
% 0.21/0.43    inference(avatar_split_clause,[],[f138,f135,f53,f297])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl3_6 <=> ! [X1,X0,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f138,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2)) ) | (~spl3_6 | ~spl3_16)),
% 0.21/0.43    inference(superposition,[],[f54,f136])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f53])).
% 0.21/0.43  fof(f146,plain,(
% 0.21/0.43    spl3_18 | ~spl3_3 | ~spl3_8 | ~spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f93,f70,f62,f41,f144])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl3_3 <=> ! [X1,X0] : k1_mcart_1(k4_tarski(X0,X1)) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl3_8 <=> ! [X1,X3,X0,X2] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    spl3_10 <=> ! [X1,X3,X0,X2] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    ( ! [X6,X4,X5] : (k3_mcart_1(X4,X5,X6) = k4_tarski(k4_tarski(X4,X5),X6)) ) | (~spl3_3 | ~spl3_8 | ~spl3_10)),
% 0.21/0.43    inference(forward_demodulation,[],[f91,f74])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X6,X4,X7,X5] : (k3_mcart_1(X4,X5,X6) = k1_mcart_1(k4_mcart_1(X4,X5,X6,X7))) ) | (~spl3_3 | ~spl3_8)),
% 0.21/0.43    inference(superposition,[],[f42,f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) ) | ~spl3_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f62])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) ) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f41])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    ( ! [X6,X4,X7,X5] : (k1_mcart_1(k4_mcart_1(X4,X5,X6,X7)) = k4_tarski(k4_tarski(X4,X5),X6)) ) | (~spl3_3 | ~spl3_10)),
% 0.21/0.43    inference(superposition,[],[f42,f71])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) ) | ~spl3_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f70])).
% 0.21/0.43  fof(f137,plain,(
% 0.21/0.43    spl3_16 | ~spl3_2 | ~spl3_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f110,f80,f37,f135])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl3_2 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl3_12 <=> ! [X1,X0,X2] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    ( ! [X4,X3] : (k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4))) ) | (~spl3_2 | ~spl3_12)),
% 0.21/0.43    inference(forward_demodulation,[],[f102,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f37])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    ( ! [X4,X3] : (k1_tarski(k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X4))) ) | (~spl3_2 | ~spl3_12)),
% 0.21/0.43    inference(superposition,[],[f81,f38])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) ) | ~spl3_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f80])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl3_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f80])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f70])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f62])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f41])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f37])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f32])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2)) => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.21/0.43    inference(negated_conjecture,[],[f12])).
% 0.21/0.43  fof(f12,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (29749)------------------------------
% 0.21/0.43  % (29749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (29749)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (29749)Memory used [KB]: 6396
% 0.21/0.43  % (29749)Time elapsed: 0.033 s
% 0.21/0.43  % (29749)------------------------------
% 0.21/0.43  % (29749)------------------------------
% 0.21/0.43  % (29740)Success in time 0.072 s
%------------------------------------------------------------------------------
