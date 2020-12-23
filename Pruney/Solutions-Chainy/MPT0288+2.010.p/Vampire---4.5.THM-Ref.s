%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 120 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :    5
%              Number of atoms          :  195 ( 292 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f55,f63,f67,f73,f83,f89,f233,f257,f291,f320,f327,f329])).

fof(f329,plain,
    ( ~ spl4_35
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl4_35
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f256,f290])).

fof(f290,plain,
    ( ! [X1] : ~ r2_hidden(sK2(sK0,k3_tarski(sK1)),X1)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl4_40
  <=> ! [X1] : ~ r2_hidden(sK2(sK0,k3_tarski(sK1)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f256,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k1_xboole_0)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl4_35
  <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f327,plain,
    ( spl4_2
    | ~ spl4_10
    | ~ spl4_43 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl4_2
    | ~ spl4_10
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f323,f34])).

fof(f34,plain,
    ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_2
  <=> r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f323,plain,
    ( r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
    | ~ spl4_10
    | ~ spl4_43 ),
    inference(resolution,[],[f319,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2(X0,X1),X1)
        | r1_tarski(k3_tarski(X0),X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK2(X0,X1),X1)
        | r1_tarski(k3_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f319,plain,
    ( r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl4_43
  <=> r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f320,plain,
    ( spl4_43
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f298,f252,f41,f318])).

fof(f41,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | r1_tarski(X0,k3_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f252,plain,
    ( spl4_34
  <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f298,plain,
    ( r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(resolution,[],[f253,f42])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | r1_tarski(X0,k3_tarski(X1)) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f253,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f252])).

fof(f291,plain,
    ( spl4_40
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f267,f255,f53,f37,f289])).

fof(f37,plain,
    ( spl4_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f53,plain,
    ( spl4_7
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f267,plain,
    ( ! [X1] : ~ r2_hidden(sK2(sK0,k3_tarski(sK1)),X1)
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f265,f38])).

fof(f38,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f265,plain,
    ( ! [X1] : ~ r2_hidden(sK2(sK0,k3_tarski(sK1)),k4_xboole_0(X1,k1_xboole_0))
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(resolution,[],[f256,f54])).

fof(f54,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f257,plain,
    ( spl4_34
    | spl4_35
    | ~ spl4_11
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f243,f231,f71,f255,f252])).

fof(f71,plain,
    ( spl4_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f231,plain,
    ( spl4_31
  <=> ! [X0] :
        ( r2_hidden(sK2(sK0,k3_tarski(sK1)),X0)
        | r2_hidden(sK2(sK0,k3_tarski(sK1)),k4_xboole_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f243,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k1_xboole_0)
    | r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1)
    | ~ spl4_11
    | ~ spl4_31 ),
    inference(superposition,[],[f232,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f232,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k4_xboole_0(sK0,X0))
        | r2_hidden(sK2(sK0,k3_tarski(sK1)),X0) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f231])).

fof(f233,plain,
    ( spl4_31
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f90,f87,f81,f231])).

fof(f81,plain,
    ( spl4_12
  <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f87,plain,
    ( spl4_13
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,X1)
        | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f90,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,k3_tarski(sK1)),X0)
        | r2_hidden(sK2(sK0,k3_tarski(sK1)),k4_xboole_0(sK0,X0)) )
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(resolution,[],[f88,f82])).

fof(f82,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f88,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,X1)
        | r2_hidden(X3,k4_xboole_0(X0,X1)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f25,f87])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f83,plain,
    ( spl4_12
    | spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f78,f61,f33,f81])).

fof(f61,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_tarski(k3_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f78,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0)
    | spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f62,f34])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_tarski(X0),X1)
        | r2_hidden(sK2(X0,X1),X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f73,plain,
    ( spl4_11
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f68,f45,f29,f71])).

fof(f29,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f45,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(resolution,[],[f46,f30])).

fof(f30,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f67,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f16,f65])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f63,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f15,f61])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f17,f45])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f43,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f14,f41])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f13,f37])).

fof(f13,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f35,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f12,f33])).

fof(f12,plain,(
    ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f31,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f11,f29])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:18:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (23388)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (23388)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f330,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f55,f63,f67,f73,f83,f89,f233,f257,f291,f320,f327,f329])).
% 0.21/0.47  fof(f329,plain,(
% 0.21/0.47    ~spl4_35 | ~spl4_40),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f328])).
% 0.21/0.47  fof(f328,plain,(
% 0.21/0.47    $false | (~spl4_35 | ~spl4_40)),
% 0.21/0.47    inference(subsumption_resolution,[],[f256,f290])).
% 0.21/0.47  fof(f290,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(sK2(sK0,k3_tarski(sK1)),X1)) ) | ~spl4_40),
% 0.21/0.47    inference(avatar_component_clause,[],[f289])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    spl4_40 <=> ! [X1] : ~r2_hidden(sK2(sK0,k3_tarski(sK1)),X1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0,k3_tarski(sK1)),k1_xboole_0) | ~spl4_35),
% 0.21/0.47    inference(avatar_component_clause,[],[f255])).
% 0.21/0.47  fof(f255,plain,(
% 0.21/0.47    spl4_35 <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.47  fof(f327,plain,(
% 0.21/0.47    spl4_2 | ~spl4_10 | ~spl4_43),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f326])).
% 0.21/0.47  fof(f326,plain,(
% 0.21/0.47    $false | (spl4_2 | ~spl4_10 | ~spl4_43)),
% 0.21/0.47    inference(subsumption_resolution,[],[f323,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) | spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    spl4_2 <=> r1_tarski(k3_tarski(sK0),k3_tarski(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f323,plain,(
% 0.21/0.47    r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) | (~spl4_10 | ~spl4_43)),
% 0.21/0.47    inference(resolution,[],[f319,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) ) | ~spl4_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl4_10 <=> ! [X1,X0] : (~r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) | ~spl4_43),
% 0.21/0.47    inference(avatar_component_clause,[],[f318])).
% 0.21/0.47  fof(f318,plain,(
% 0.21/0.47    spl4_43 <=> r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.47  fof(f320,plain,(
% 0.21/0.47    spl4_43 | ~spl4_4 | ~spl4_34),
% 0.21/0.47    inference(avatar_split_clause,[],[f298,f252,f41,f318])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl4_4 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f252,plain,(
% 0.21/0.47    spl4_34 <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.47  fof(f298,plain,(
% 0.21/0.47    r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) | (~spl4_4 | ~spl4_34)),
% 0.21/0.47    inference(resolution,[],[f253,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) ) | ~spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f253,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1) | ~spl4_34),
% 0.21/0.47    inference(avatar_component_clause,[],[f252])).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    spl4_40 | ~spl4_3 | ~spl4_7 | ~spl4_35),
% 0.21/0.47    inference(avatar_split_clause,[],[f267,f255,f53,f37,f289])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl4_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl4_7 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.47  fof(f267,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(sK2(sK0,k3_tarski(sK1)),X1)) ) | (~spl4_3 | ~spl4_7 | ~spl4_35)),
% 0.21/0.47    inference(forward_demodulation,[],[f265,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f37])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(sK2(sK0,k3_tarski(sK1)),k4_xboole_0(X1,k1_xboole_0))) ) | (~spl4_7 | ~spl4_35)),
% 0.21/0.47    inference(resolution,[],[f256,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) ) | ~spl4_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f257,plain,(
% 0.21/0.47    spl4_34 | spl4_35 | ~spl4_11 | ~spl4_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f243,f231,f71,f255,f252])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl4_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    spl4_31 <=> ! [X0] : (r2_hidden(sK2(sK0,k3_tarski(sK1)),X0) | r2_hidden(sK2(sK0,k3_tarski(sK1)),k4_xboole_0(sK0,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.47  fof(f243,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0,k3_tarski(sK1)),k1_xboole_0) | r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1) | (~spl4_11 | ~spl4_31)),
% 0.21/0.47    inference(superposition,[],[f232,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl4_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f232,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK2(sK0,k3_tarski(sK1)),k4_xboole_0(sK0,X0)) | r2_hidden(sK2(sK0,k3_tarski(sK1)),X0)) ) | ~spl4_31),
% 0.21/0.47    inference(avatar_component_clause,[],[f231])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    spl4_31 | ~spl4_12 | ~spl4_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f90,f87,f81,f231])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl4_12 <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl4_13 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK2(sK0,k3_tarski(sK1)),X0) | r2_hidden(sK2(sK0,k3_tarski(sK1)),k4_xboole_0(sK0,X0))) ) | (~spl4_12 | ~spl4_13)),
% 0.21/0.47    inference(resolution,[],[f88,f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0) | ~spl4_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) ) | ~spl4_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f87])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl4_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f87])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl4_12 | spl4_2 | ~spl4_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f78,f61,f33,f81])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl4_9 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0) | (spl4_2 | ~spl4_9)),
% 0.21/0.47    inference(resolution,[],[f62,f34])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0)) ) | ~spl4_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl4_11 | ~spl4_1 | ~spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f68,f45,f29,f71])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    spl4_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl4_5 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl4_1 | ~spl4_5)),
% 0.21/0.47    inference(resolution,[],[f46,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f29])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f65])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f61])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f53])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f45])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f41])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f37])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f12,f33])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f29])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (23388)------------------------------
% 0.21/0.48  % (23388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23388)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (23388)Memory used [KB]: 10746
% 0.21/0.48  % (23388)Time elapsed: 0.022 s
% 0.21/0.48  % (23388)------------------------------
% 0.21/0.48  % (23388)------------------------------
% 0.21/0.48  % (23372)Success in time 0.118 s
%------------------------------------------------------------------------------
