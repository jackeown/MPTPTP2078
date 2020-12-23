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
% DateTime   : Thu Dec  3 12:31:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 111 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  184 ( 276 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f71,f81,f88,f116,f154,f169,f172])).

fof(f172,plain,
    ( spl5_2
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_15
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl5_2
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_15
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f41,f170])).

fof(f170,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_15
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f168,f164])).

fof(f164,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f162,f50])).

fof(f50,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f162,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl5_9
    | ~ spl5_15 ),
    inference(superposition,[],[f70,f115])).

fof(f115,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_15
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f70,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_9
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f168,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl5_20
  <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f41,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f169,plain,
    ( spl5_20
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f155,f152,f44,f166])).

fof(f44,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f152,plain,
    ( spl5_19
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,k2_xboole_0(X1,X0))
        | r1_tarski(k4_xboole_0(X2,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f155,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f46,f153])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,k2_xboole_0(X1,X0))
        | r1_tarski(k4_xboole_0(X2,X0),X1) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f152])).

fof(f46,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f154,plain,
    ( spl5_19
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f94,f79,f57,f152])).

fof(f57,plain,
    ( spl5_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f79,plain,
    ( spl5_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f94,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,k2_xboole_0(X1,X0))
        | r1_tarski(k4_xboole_0(X2,X0),X1) )
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(superposition,[],[f80,f58])).

fof(f58,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | r1_tarski(k4_xboole_0(X0,X1),X2) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f116,plain,
    ( spl5_15
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f96,f86,f53,f113])).

fof(f53,plain,
    ( spl5_5
  <=> ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,
    ( spl5_12
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f96,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f87,f54])).

fof(f54,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f87,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK2))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,
    ( spl5_12
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f72,f61,f34,f86])).

fof(f34,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f61,plain,
    ( spl5_7
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f72,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK2))
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f36,f62])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f36,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f81,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f71,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f63,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f59,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f55,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f51,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f47,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f42,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f23,f34])).

fof(f23,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:04:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (3135)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.44  % (3130)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (3130)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f173,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f71,f81,f88,f116,f154,f169,f172])).
% 0.21/0.45  fof(f172,plain,(
% 0.21/0.45    spl5_2 | ~spl5_4 | ~spl5_9 | ~spl5_15 | ~spl5_20),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.45  fof(f171,plain,(
% 0.21/0.45    $false | (spl5_2 | ~spl5_4 | ~spl5_9 | ~spl5_15 | ~spl5_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f41,f170])).
% 0.21/0.45  fof(f170,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1) | (~spl5_4 | ~spl5_9 | ~spl5_15 | ~spl5_20)),
% 0.21/0.45    inference(forward_demodulation,[],[f168,f164])).
% 0.21/0.45  fof(f164,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,sK2) | (~spl5_4 | ~spl5_9 | ~spl5_15)),
% 0.21/0.45    inference(forward_demodulation,[],[f162,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl5_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.45  fof(f162,plain,(
% 0.21/0.45    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) | (~spl5_9 | ~spl5_15)),
% 0.21/0.45    inference(superposition,[],[f70,f115])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl5_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f113])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    spl5_15 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl5_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f69])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl5_9 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.45  fof(f168,plain,(
% 0.21/0.45    r1_tarski(k4_xboole_0(sK0,sK2),sK1) | ~spl5_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f166])).
% 0.21/0.45  fof(f166,plain,(
% 0.21/0.45    spl5_20 <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ~r1_tarski(sK0,sK1) | spl5_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl5_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.45  fof(f169,plain,(
% 0.21/0.45    spl5_20 | ~spl5_3 | ~spl5_19),
% 0.21/0.45    inference(avatar_split_clause,[],[f155,f152,f44,f166])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    spl5_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.45  fof(f152,plain,(
% 0.21/0.45    spl5_19 <=> ! [X1,X0,X2] : (~r1_tarski(X2,k2_xboole_0(X1,X0)) | r1_tarski(k4_xboole_0(X2,X0),X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.45  fof(f155,plain,(
% 0.21/0.45    r1_tarski(k4_xboole_0(sK0,sK2),sK1) | (~spl5_3 | ~spl5_19)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f46,f153])).
% 0.21/0.45  fof(f153,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_xboole_0(X1,X0)) | r1_tarski(k4_xboole_0(X2,X0),X1)) ) | ~spl5_19),
% 0.21/0.45    inference(avatar_component_clause,[],[f152])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f44])).
% 0.21/0.45  fof(f154,plain,(
% 0.21/0.45    spl5_19 | ~spl5_6 | ~spl5_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f94,f79,f57,f152])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    spl5_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    spl5_11 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_xboole_0(X1,X0)) | r1_tarski(k4_xboole_0(X2,X0),X1)) ) | (~spl5_6 | ~spl5_11)),
% 0.21/0.45    inference(superposition,[],[f80,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl5_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f57])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) ) | ~spl5_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f79])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    spl5_15 | ~spl5_5 | ~spl5_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f96,f86,f53,f113])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl5_5 <=> ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    spl5_12 <=> ! [X0] : ~r2_hidden(X0,k3_xboole_0(sK0,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl5_5 | ~spl5_12)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f87,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl5_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f53])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK2))) ) | ~spl5_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f86])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    spl5_12 | ~spl5_1 | ~spl5_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f72,f61,f34,f86])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    spl5_1 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl5_7 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK2))) ) | (~spl5_1 | ~spl5_7)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f36,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f61])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK2) | ~spl5_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f34])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl5_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f79])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    spl5_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f69])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    spl5_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f31,f61])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(rectify,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl5_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f57])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    spl5_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f53])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl5_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f49])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl5_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.45    inference(flattening,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f8])).
% 0.21/0.45  fof(f8,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ~spl5_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f39])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ~r1_tarski(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    spl5_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f34])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (3130)------------------------------
% 0.21/0.45  % (3130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (3130)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (3130)Memory used [KB]: 6140
% 0.21/0.45  % (3130)Time elapsed: 0.043 s
% 0.21/0.45  % (3130)------------------------------
% 0.21/0.45  % (3130)------------------------------
% 0.21/0.46  % (3138)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (3123)Success in time 0.104 s
%------------------------------------------------------------------------------
