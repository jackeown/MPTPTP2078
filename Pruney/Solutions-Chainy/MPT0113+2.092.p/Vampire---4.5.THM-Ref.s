%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 109 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :    6
%              Number of atoms          :  183 ( 267 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f45,f49,f53,f57,f61,f69,f73,f89,f101,f139,f164,f243,f354])).

fof(f354,plain,
    ( spl3_1
    | ~ spl3_14
    | ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl3_1
    | ~ spl3_14
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f343,f31])).

fof(f31,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f343,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_14
    | ~ spl3_37 ),
    inference(superposition,[],[f242,f88])).

fof(f88,plain,
    ( ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_14
  <=> ! [X1,X2] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f242,plain,
    ( ! [X2] : r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X2))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl3_37
  <=> ! [X2] : r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f243,plain,
    ( spl3_37
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f239,f98,f67,f43,f241])).

fof(f43,plain,
    ( spl3_4
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f98,plain,
    ( spl3_16
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f239,plain,
    ( ! [X2] : r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X2))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f229,f44])).

fof(f44,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f229,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,X2)
        | r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X2)) )
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(superposition,[],[f68,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f98])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
        | r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f164,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f152,f137,f38,f33])).

fof(f33,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f137,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f152,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(resolution,[],[f138,f40])).

fof(f40,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X2,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f134,f71,f47,f137])).

fof(f47,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f71,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) )
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f72,f48])).

fof(f48,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f101,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f91,f59,f38,f98])).

fof(f59,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f91,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f60,f40])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f89,plain,
    ( spl3_14
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f76,f55,f51,f87])).

fof(f51,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f55,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f56,f52])).

fof(f52,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f73,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f27,f71])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f69,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f61,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f57,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f53,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f49,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f45,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f41,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f36,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f33,f29])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (4635)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.41  % (4632)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (4632)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f355,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f36,f41,f45,f49,f53,f57,f61,f69,f73,f89,f101,f139,f164,f243,f354])).
% 0.20/0.42  fof(f354,plain,(
% 0.20/0.42    spl3_1 | ~spl3_14 | ~spl3_37),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f353])).
% 0.20/0.42  fof(f353,plain,(
% 0.20/0.42    $false | (spl3_1 | ~spl3_14 | ~spl3_37)),
% 0.20/0.42    inference(subsumption_resolution,[],[f343,f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f343,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1) | (~spl3_14 | ~spl3_37)),
% 0.20/0.42    inference(superposition,[],[f242,f88])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1) ) | ~spl3_14),
% 0.20/0.42    inference(avatar_component_clause,[],[f87])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl3_14 <=> ! [X1,X2] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.42  fof(f242,plain,(
% 0.20/0.42    ( ! [X2] : (r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X2))) ) | ~spl3_37),
% 0.20/0.42    inference(avatar_component_clause,[],[f241])).
% 0.20/0.42  fof(f241,plain,(
% 0.20/0.42    spl3_37 <=> ! [X2] : r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.42  fof(f243,plain,(
% 0.20/0.42    spl3_37 | ~spl3_4 | ~spl3_10 | ~spl3_16),
% 0.20/0.42    inference(avatar_split_clause,[],[f239,f98,f67,f43,f241])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl3_4 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    spl3_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    spl3_16 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.42  fof(f239,plain,(
% 0.20/0.42    ( ! [X2] : (r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X2))) ) | (~spl3_4 | ~spl3_10 | ~spl3_16)),
% 0.20/0.42    inference(subsumption_resolution,[],[f229,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f43])).
% 0.20/0.42  fof(f229,plain,(
% 0.20/0.42    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X2))) ) | (~spl3_10 | ~spl3_16)),
% 0.20/0.42    inference(superposition,[],[f68,f100])).
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_16),
% 0.20/0.42    inference(avatar_component_clause,[],[f98])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f67])).
% 0.20/0.42  fof(f164,plain,(
% 0.20/0.42    spl3_2 | ~spl3_3 | ~spl3_21),
% 0.20/0.42    inference(avatar_split_clause,[],[f152,f137,f38,f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl3_3 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f137,plain,(
% 0.20/0.42    spl3_21 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.42  fof(f152,plain,(
% 0.20/0.42    r1_xboole_0(sK0,sK2) | (~spl3_3 | ~spl3_21)),
% 0.20/0.42    inference(resolution,[],[f138,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f38])).
% 0.20/0.42  fof(f138,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X2,X1)) | r1_xboole_0(X0,X1)) ) | ~spl3_21),
% 0.20/0.42    inference(avatar_component_clause,[],[f137])).
% 0.20/0.42  fof(f139,plain,(
% 0.20/0.42    spl3_21 | ~spl3_5 | ~spl3_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f134,f71,f47,f137])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    spl3_5 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl3_11 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.42  fof(f134,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X2,X1))) ) | (~spl3_5 | ~spl3_11)),
% 0.20/0.42    inference(resolution,[],[f72,f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f47])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f71])).
% 0.20/0.42  fof(f101,plain,(
% 0.20/0.42    spl3_16 | ~spl3_3 | ~spl3_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f91,f59,f38,f98])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl3_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.42  fof(f91,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_8)),
% 0.20/0.42    inference(resolution,[],[f60,f40])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f59])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    spl3_14 | ~spl3_6 | ~spl3_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f76,f55,f51,f87])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl3_6 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl3_7 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1) ) | (~spl3_6 | ~spl3_7)),
% 0.20/0.42    inference(resolution,[],[f56,f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f51])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f55])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    spl3_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f71])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    spl3_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f67])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl3_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f59])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.42    inference(nnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl3_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f55])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f51])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f47])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f43])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    spl3_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f38])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.42    inference(negated_conjecture,[],[f8])).
% 0.20/0.42  fof(f8,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ~spl3_1 | ~spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f33,f29])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (4632)------------------------------
% 0.20/0.42  % (4632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (4632)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (4632)Memory used [KB]: 10746
% 0.20/0.42  % (4632)Time elapsed: 0.009 s
% 0.20/0.42  % (4632)------------------------------
% 0.20/0.42  % (4632)------------------------------
% 0.20/0.42  % (4626)Success in time 0.066 s
%------------------------------------------------------------------------------
