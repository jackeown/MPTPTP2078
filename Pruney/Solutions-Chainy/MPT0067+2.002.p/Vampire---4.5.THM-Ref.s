%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  90 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :  122 ( 182 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f49,f56,f71,f76,f94,f110,f121])).

fof(f121,plain,(
    ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl2_11 ),
    inference(resolution,[],[f109,f19])).

fof(f19,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f109,plain,
    ( r2_xboole_0(sK0,sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_11
  <=> r2_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f110,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f101,f86,f29,f108])).

fof(f29,plain,
    ( spl2_1
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,
    ( spl2_8
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f101,plain,
    ( r2_xboole_0(sK0,sK0)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(superposition,[],[f30,f87])).

fof(f87,plain,
    ( sK0 = sK1
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f30,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f94,plain,
    ( spl2_8
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f93,f74,f69,f86])).

fof(f69,plain,
    ( spl2_6
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f74,plain,
    ( spl2_7
  <=> sK0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f93,plain,
    ( sK0 = sK1
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f83,f75])).

fof(f75,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f83,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl2_6 ),
    inference(superposition,[],[f20,f70])).

fof(f70,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f76,plain,
    ( spl2_7
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f72,f54,f74])).

fof(f54,plain,
    ( spl2_4
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f72,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f64,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f64,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_4 ),
    inference(superposition,[],[f21,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f71,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f67,f47,f69])).

fof(f47,plain,
    ( spl2_3
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f63,f18])).

fof(f63,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f21,f48])).

fof(f48,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f56,plain,
    ( spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f52,f29,f54])).

fof(f52,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f45,f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f49,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f44,f33,f47])).

fof(f33,plain,
    ( spl2_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f44,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f26,f34])).

fof(f34,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( r2_xboole_0(sK1,sK0)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) )
   => ( r2_xboole_0(sK1,sK0)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( r2_xboole_0(X1,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_xboole_0(X1,X0)
          & r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f31,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:03:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (6393)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.42  % (6393)Refutation not found, incomplete strategy% (6393)------------------------------
% 0.21/0.42  % (6393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (6393)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (6393)Memory used [KB]: 1535
% 0.21/0.42  % (6393)Time elapsed: 0.002 s
% 0.21/0.42  % (6393)------------------------------
% 0.21/0.42  % (6393)------------------------------
% 0.21/0.45  % (6386)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.45  % (6386)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f122,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f31,f35,f49,f56,f71,f76,f94,f110,f121])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    ~spl2_11),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    $false | ~spl2_11),
% 0.21/0.45    inference(resolution,[],[f109,f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ! [X0] : ~r2_xboole_0(X0,X0)),
% 0.21/0.45    inference(rectify,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    r2_xboole_0(sK0,sK0) | ~spl2_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f108])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    spl2_11 <=> r2_xboole_0(sK0,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    spl2_11 | ~spl2_1 | ~spl2_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f101,f86,f29,f108])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    spl2_1 <=> r2_xboole_0(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    spl2_8 <=> sK0 = sK1),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    r2_xboole_0(sK0,sK0) | (~spl2_1 | ~spl2_8)),
% 0.21/0.45    inference(superposition,[],[f30,f87])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    sK0 = sK1 | ~spl2_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f86])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    r2_xboole_0(sK1,sK0) | ~spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f29])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    spl2_8 | ~spl2_6 | ~spl2_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f93,f74,f69,f86])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl2_6 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    spl2_7 <=> sK0 = k2_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    sK0 = sK1 | (~spl2_6 | ~spl2_7)),
% 0.21/0.45    inference(forward_demodulation,[],[f83,f75])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    sK0 = k2_xboole_0(sK0,sK1) | ~spl2_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f74])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    sK1 = k2_xboole_0(sK0,sK1) | ~spl2_6),
% 0.21/0.45    inference(superposition,[],[f20,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    sK1 = k2_xboole_0(sK1,sK0) | ~spl2_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f69])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl2_7 | ~spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f72,f54,f74])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    spl2_4 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    sK0 = k2_xboole_0(sK0,sK1) | ~spl2_4),
% 0.21/0.45    inference(forward_demodulation,[],[f64,f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0) | ~spl2_4),
% 0.21/0.45    inference(superposition,[],[f21,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f54])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    spl2_6 | ~spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f67,f47,f69])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl2_3 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    sK1 = k2_xboole_0(sK1,sK0) | ~spl2_3),
% 0.21/0.45    inference(forward_demodulation,[],[f63,f18])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) | ~spl2_3),
% 0.21/0.45    inference(superposition,[],[f21,f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f47])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl2_4 | ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f52,f29,f54])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_1),
% 0.21/0.45    inference(resolution,[],[f45,f30])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.45    inference(resolution,[],[f26,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.45    inference(flattening,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.45    inference(nnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl2_3 | ~spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f44,f33,f47])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    spl2_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl2_2),
% 0.21/0.45    inference(resolution,[],[f26,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1) | ~spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f33])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f16,f33])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    r2_xboole_0(sK1,sK0) & r1_tarski(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1] : (r2_xboole_0(X1,X0) & r1_tarski(X0,X1)) => (r2_xboole_0(sK1,sK0) & r1_tarski(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0,X1] : (r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f7])).
% 0.21/0.45  fof(f7,conjecture,(
% 0.21/0.45    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f17,f29])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    r2_xboole_0(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (6386)------------------------------
% 0.21/0.45  % (6386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (6386)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (6386)Memory used [KB]: 10618
% 0.21/0.45  % (6386)Time elapsed: 0.006 s
% 0.21/0.45  % (6386)------------------------------
% 0.21/0.45  % (6386)------------------------------
% 0.21/0.46  % (6379)Success in time 0.092 s
%------------------------------------------------------------------------------
