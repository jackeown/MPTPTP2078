%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 109 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :    6
%              Number of atoms          :  182 ( 286 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f49,f53,f57,f61,f65,f69,f86,f99,f139,f147,f173,f196,f205])).

fof(f205,plain,
    ( ~ spl10_2
    | ~ spl10_8
    | spl10_27 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_8
    | spl10_27 ),
    inference(unit_resulting_resolution,[],[f41,f195,f64])).

fof(f64,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k2_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X3,X2),X0) )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl10_8
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X3,X2),X0)
        | r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f195,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | spl10_27 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl10_27
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f41,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl10_2
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f196,plain,
    ( ~ spl10_27
    | spl10_3
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f182,f171,f44,f194])).

fof(f44,plain,
    ( spl10_3
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f171,plain,
    ( spl10_25
  <=> ! [X1] :
        ( r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f182,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | spl10_3
    | ~ spl10_25 ),
    inference(resolution,[],[f172,f45])).

fof(f45,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f172,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f171])).

fof(f173,plain,
    ( spl10_25
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f88,f84,f51,f171])).

fof(f51,plain,
    ( spl10_5
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f84,plain,
    ( spl10_13
  <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f88,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(superposition,[],[f52,f85])).

fof(f85,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f52,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,k2_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X1) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f147,plain,
    ( ~ spl10_2
    | ~ spl10_7
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_7
    | spl10_21 ),
    inference(unit_resulting_resolution,[],[f41,f138,f60])).

fof(f60,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k1_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X2,X3),X0) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl10_7
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),X0)
        | r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f138,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl10_21 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl10_21
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f139,plain,
    ( ~ spl10_21
    | spl10_4
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f105,f97,f47,f137])).

fof(f47,plain,
    ( spl10_4
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f97,plain,
    ( spl10_15
  <=> ! [X0] :
        ( r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f105,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl10_4
    | ~ spl10_15 ),
    inference(resolution,[],[f98,f48])).

fof(f48,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f98,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f99,plain,
    ( spl10_15
    | ~ spl10_6
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f87,f84,f55,f97])).

fof(f55,plain,
    ( spl10_6
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f87,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl10_6
    | ~ spl10_13 ),
    inference(superposition,[],[f56,f85])).

fof(f56,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,k2_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X0) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f86,plain,
    ( spl10_13
    | ~ spl10_1
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f82,f67,f36,f84])).

fof(f36,plain,
    ( spl10_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f67,plain,
    ( spl10_9
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f82,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl10_1
    | ~ spl10_9 ),
    inference(resolution,[],[f68,f37])).

fof(f37,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) )
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f13,f67])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f65,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f61,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f57,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f53,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f32,f51])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f49,plain,
    ( ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f10,f47,f44])).

fof(f10,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f42,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f12,f40])).

fof(f12,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f11,f36])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (21179)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (21188)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.47  % (21175)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (21184)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (21179)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f38,f42,f49,f53,f57,f61,f65,f69,f86,f99,f139,f147,f173,f196,f205])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    ~spl10_2 | ~spl10_8 | spl10_27),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f201])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    $false | (~spl10_2 | ~spl10_8 | spl10_27)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f41,f195,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X2,X0,X3] : (r2_hidden(X2,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0)) ) | ~spl10_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl10_8 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k2_relat_1(sK2)) | spl10_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f194])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    spl10_27 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl10_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl10_2 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    ~spl10_27 | spl10_3 | ~spl10_25),
% 0.22/0.49    inference(avatar_split_clause,[],[f182,f171,f44,f194])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl10_3 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    spl10_25 <=> ! [X1] : (r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X1,k2_relat_1(sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k2_relat_1(sK2)) | (spl10_3 | ~spl10_25)),
% 0.22/0.49    inference(resolution,[],[f172,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k3_relat_1(sK2)) | spl10_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f44])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ( ! [X1] : (r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl10_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f171])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    spl10_25 | ~spl10_5 | ~spl10_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f88,f84,f51,f171])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl10_5 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl10_13 <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X1] : (r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | (~spl10_5 | ~spl10_13)),
% 0.22/0.49    inference(superposition,[],[f52,f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl10_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f84])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) ) | ~spl10_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f51])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    ~spl10_2 | ~spl10_7 | spl10_21),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f144])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    $false | (~spl10_2 | ~spl10_7 | spl10_21)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f41,f138,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) ) | ~spl10_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl10_7 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl10_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f137])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    spl10_21 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~spl10_21 | spl10_4 | ~spl10_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f105,f97,f47,f137])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    spl10_4 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl10_15 <=> ! [X0] : (r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(sK2)) | (spl10_4 | ~spl10_15)),
% 0.22/0.49    inference(resolution,[],[f98,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k3_relat_1(sK2)) | spl10_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f47])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl10_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f97])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl10_15 | ~spl10_6 | ~spl10_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f87,f84,f55,f97])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl10_6 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2))) ) | (~spl10_6 | ~spl10_13)),
% 0.22/0.49    inference(superposition,[],[f56,f85])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) ) | ~spl10_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f55])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl10_13 | ~spl10_1 | ~spl10_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f82,f67,f36,f84])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    spl10_1 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl10_9 <=> ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl10_1 | ~spl10_9)),
% 0.22/0.49    inference(resolution,[],[f68,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    v1_relat_1(sK2) | ~spl10_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f36])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) ) | ~spl10_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f67])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl10_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f13,f67])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl10_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f63])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl10_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f59])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl10_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f55])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl10_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f51])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ~spl10_3 | ~spl10_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f10,f47,f44])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2) & v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (((~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2))) & r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f5])).
% 0.22/0.49  fof(f5,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    spl10_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f12,f40])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl10_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f11,f36])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (21179)------------------------------
% 0.22/0.49  % (21179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21179)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (21179)Memory used [KB]: 10746
% 0.22/0.49  % (21179)Time elapsed: 0.060 s
% 0.22/0.49  % (21179)------------------------------
% 0.22/0.49  % (21179)------------------------------
% 0.22/0.49  % (21169)Success in time 0.122 s
%------------------------------------------------------------------------------
