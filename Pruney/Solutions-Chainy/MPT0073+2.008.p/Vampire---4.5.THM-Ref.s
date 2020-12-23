%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  83 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  156 ( 224 expanded)
%              Number of equality atoms :   25 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f141,f144,f195])).

fof(f195,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f192,f36])).

fof(f36,plain,(
    ! [X0] : sQ3_eqProxy(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(equality_proxy_replacement,[],[f24,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f192,plain,
    ( ~ sQ3_eqProxy(k1_xboole_0,k3_xboole_0(sK0,k1_xboole_0))
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f176,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f32])).

fof(f176,plain,
    ( ~ sQ3_eqProxy(k3_xboole_0(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f164,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ sQ3_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f164,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f157,f45])).

fof(f45,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f32])).

fof(f157,plain,
    ( ! [X6] :
        ( ~ sQ3_eqProxy(X6,sK0)
        | ~ r1_xboole_0(X6,k1_xboole_0) )
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f148,f51])).

fof(f51,plain,
    ( sQ3_eqProxy(k1_xboole_0,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_1
  <=> sQ3_eqProxy(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f148,plain,
    ( ! [X2,X3] :
        ( ~ sQ3_eqProxy(X2,sK0)
        | ~ r1_xboole_0(X3,X2)
        | ~ sQ3_eqProxy(X3,sK0) )
    | spl4_2 ),
    inference(resolution,[],[f54,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X1,X3)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ r1_xboole_0(X0,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f32])).

fof(f54,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f144,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f142,f51])).

fof(f142,plain,
    ( ~ sQ3_eqProxy(k1_xboole_0,sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f35,f55])).

fof(f55,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f35,plain,
    ( ~ sQ3_eqProxy(k1_xboole_0,sK0)
    | ~ r1_xboole_0(sK0,sK0) ),
    inference(equality_proxy_replacement,[],[f20,f32])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_xboole_0(sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( r1_xboole_0(sK0,sK0)
      & k1_xboole_0 != sK0 )
    | ( k1_xboole_0 = sK0
      & ~ r1_xboole_0(sK0,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
        | ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) )
   => ( ( r1_xboole_0(sK0,sK0)
        & k1_xboole_0 != sK0 )
      | ( k1_xboole_0 = sK0
        & ~ r1_xboole_0(sK0,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ ( r1_xboole_0(X0,X0)
            & k1_xboole_0 != X0 )
        & ~ ( k1_xboole_0 = X0
            & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f141,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f133,f50])).

fof(f50,plain,
    ( ~ sQ3_eqProxy(k1_xboole_0,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f133,plain,
    ( sQ3_eqProxy(k1_xboole_0,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f103,f55])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | sQ3_eqProxy(k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | sQ3_eqProxy(k1_xboole_0,X0)
      | sQ3_eqProxy(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | sQ3_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f25,f32])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X1),X0)
      | ~ r1_xboole_0(X0,X1)
      | sQ3_eqProxy(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f56,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f33,f53,f49])).

fof(f33,plain,
    ( r1_xboole_0(sK0,sK0)
    | sQ3_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f23,f32])).

fof(f23,plain,
    ( r1_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:59:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (8523)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (8521)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (8521)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (8531)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (8529)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (8529)Refutation not found, incomplete strategy% (8529)------------------------------
% 0.21/0.48  % (8529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8531)Refutation not found, incomplete strategy% (8531)------------------------------
% 0.21/0.48  % (8531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8531)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8531)Memory used [KB]: 6140
% 0.21/0.48  % (8531)Time elapsed: 0.066 s
% 0.21/0.48  % (8531)------------------------------
% 0.21/0.48  % (8531)------------------------------
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f56,f141,f144,f195])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    ~spl4_1 | spl4_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f194])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    $false | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f192,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f24,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k1_xboole_0,k3_xboole_0(sK0,k1_xboole_0)) | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(resolution,[],[f176,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f32])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k3_xboole_0(sK0,k1_xboole_0),k1_xboole_0) | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(resolution,[],[f164,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~sQ3_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f31,f32])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,k1_xboole_0) | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(resolution,[],[f157,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f32])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ( ! [X6] : (~sQ3_eqProxy(X6,sK0) | ~r1_xboole_0(X6,k1_xboole_0)) ) | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(resolution,[],[f148,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    sQ3_eqProxy(k1_xboole_0,sK0) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl4_1 <=> sQ3_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~sQ3_eqProxy(X2,sK0) | ~r1_xboole_0(X3,X2) | ~sQ3_eqProxy(X3,sK0)) ) | spl4_2),
% 0.21/0.48    inference(resolution,[],[f54,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X1,X3) | ~sQ3_eqProxy(X2,X3) | ~r1_xboole_0(X0,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f32])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,sK0) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl4_2 <=> r1_xboole_0(sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f143])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    $false | (~spl4_1 | ~spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f142,f51])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k1_xboole_0,sK0) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f35,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK0) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f53])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k1_xboole_0,sK0) | ~r1_xboole_0(sK0,sK0)),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f20,f32])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | ~r1_xboole_0(sK0,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    (r1_xboole_0(sK0,sK0) & k1_xboole_0 != sK0) | (k1_xboole_0 = sK0 & ~r1_xboole_0(sK0,sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0))) => ((r1_xboole_0(sK0,sK0) & k1_xboole_0 != sK0) | (k1_xboole_0 = sK0 & ~r1_xboole_0(sK0,sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl4_1 | ~spl4_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    $false | (spl4_1 | ~spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k1_xboole_0,sK0) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    sQ3_eqProxy(k1_xboole_0,sK0) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f103,f55])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_xboole_0(X0,X0) | sQ3_eqProxy(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_xboole_0(X0,X0) | sQ3_eqProxy(k1_xboole_0,X0) | sQ3_eqProxy(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f59,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | sQ3_eqProxy(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f25,f32])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK1(X1),X0) | ~r1_xboole_0(X0,X1) | sQ3_eqProxy(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f28,f37])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl4_1 | spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f53,f49])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK0) | sQ3_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f23,f32])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK0) | k1_xboole_0 = sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (8521)------------------------------
% 0.21/0.48  % (8521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8521)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (8521)Memory used [KB]: 6140
% 0.21/0.48  % (8521)Time elapsed: 0.060 s
% 0.21/0.48  % (8521)------------------------------
% 0.21/0.48  % (8521)------------------------------
% 0.21/0.48  % (8529)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  % (8515)Success in time 0.12 s
%------------------------------------------------------------------------------
