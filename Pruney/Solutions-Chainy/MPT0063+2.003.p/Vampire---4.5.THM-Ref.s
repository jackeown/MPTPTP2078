%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 127 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  201 ( 317 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f35,f43,f47,f51,f61,f65,f69,f73,f80,f90,f96,f100,f134,f148,f179])).

fof(f179,plain,
    ( ~ spl3_1
    | spl3_3
    | spl3_11
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | spl3_11
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f164,f26])).

fof(f26,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f164,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl3_3
    | spl3_11
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f68,f161])).

fof(f161,plain,
    ( sK0 = sK2
    | spl3_3
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f158,f34])).

fof(f34,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f158,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2)
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(resolution,[],[f147,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f147,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_23
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f68,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_11
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f148,plain,
    ( spl3_23
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f138,f132,f94,f146])).

fof(f94,plain,
    ( spl3_16
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f132,plain,
    ( spl3_21
  <=> ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f138,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(superposition,[],[f133,f95])).

fof(f95,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f94])).

fof(f133,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( spl3_21
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f104,f98,f49,f132])).

fof(f49,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f98,plain,
    ( spl3_17
  <=> ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f104,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(superposition,[],[f99,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f99,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f91,f88,f25,f98])).

fof(f88,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r2_xboole_0(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f91,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,sK1))
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(resolution,[],[f89,f26])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_xboole_0(X0,X2)
        | r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f88])).

fof(f96,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f82,f78,f29,f94])).

fof(f29,plain,
    ( spl3_2
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f82,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(resolution,[],[f79,f30])).

fof(f30,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r2_xboole_0(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f78])).

fof(f90,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f75,f63,f45,f88])).

fof(f45,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f63,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r2_xboole_0(X0,X2) )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f64,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r2_xboole_0(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X0,k2_xboole_0(X2,X1)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f63])).

fof(f80,plain,
    ( spl3_13
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f74,f59,f45,f78])).

fof(f59,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r2_xboole_0(X0,X1) )
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(resolution,[],[f60,f46])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f73,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f21,f71])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f69,plain,
    ( ~ spl3_11
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f53,f41,f29,f67])).

fof(f41,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r2_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f53,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f42,f30])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r2_xboole_0(X1,X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f65,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f22,f63])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f61,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f17,f59])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f51,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f16,f49])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f47,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f35,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).

fof(f31,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:34:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (23502)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (23494)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (23493)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (23494)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f27,f31,f35,f43,f47,f51,f61,f65,f69,f73,f80,f90,f96,f100,f134,f148,f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ~spl3_1 | spl3_3 | spl3_11 | ~spl3_12 | ~spl3_23),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    $false | (~spl3_1 | spl3_3 | spl3_11 | ~spl3_12 | ~spl3_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f164,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    r2_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    spl3_1 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ~r2_xboole_0(sK0,sK1) | (spl3_3 | spl3_11 | ~spl3_12 | ~spl3_23)),
% 0.21/0.49    inference(backward_demodulation,[],[f68,f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    sK0 = sK2 | (spl3_3 | ~spl3_12 | ~spl3_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f158,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ~r2_xboole_0(sK0,sK2) | spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl3_3 <=> r2_xboole_0(sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    sK0 = sK2 | r2_xboole_0(sK0,sK2) | (~spl3_12 | ~spl3_23)),
% 0.21/0.49    inference(resolution,[],[f147,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) ) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl3_12 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    r1_tarski(sK0,sK2) | ~spl3_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl3_23 <=> r1_tarski(sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~r2_xboole_0(sK2,sK1) | spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_11 <=> r2_xboole_0(sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl3_23 | ~spl3_16 | ~spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f138,f132,f94,f146])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl3_16 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl3_21 <=> ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    r1_tarski(sK0,sK2) | (~spl3_16 | ~spl3_21)),
% 0.21/0.49    inference(superposition,[],[f133,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,X0))) ) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f132])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl3_21 | ~spl3_7 | ~spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f104,f98,f49,f132])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl3_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    spl3_17 <=> ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,X0))) ) | (~spl3_7 | ~spl3_17)),
% 0.21/0.49    inference(superposition,[],[f99,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,sK1))) ) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f98])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl3_17 | ~spl3_1 | ~spl3_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f88,f25,f98])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl3_15 <=> ! [X1,X0,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r2_xboole_0(X0,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,sK1))) ) | (~spl3_1 | ~spl3_15)),
% 0.21/0.49    inference(resolution,[],[f89,f26])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_xboole_0(X0,X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_16 | ~spl3_2 | ~spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f82,f78,f29,f94])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    spl3_2 <=> r2_xboole_0(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl3_13 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r2_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    sK2 = k2_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_13)),
% 0.21/0.49    inference(resolution,[],[f79,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    r2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f29])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl3_15 | ~spl3_6 | ~spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f75,f63,f45,f88])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl3_6 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl3_10 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r2_xboole_0(X0,X2)) ) | (~spl3_6 | ~spl3_10)),
% 0.21/0.49    inference(resolution,[],[f64,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) ) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) ) | ~spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl3_13 | ~spl3_6 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f74,f59,f45,f78])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_9 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r2_xboole_0(X0,X1)) ) | (~spl3_6 | ~spl3_9)),
% 0.21/0.49    inference(resolution,[],[f60,f46])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f71])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~spl3_11 | ~spl3_2 | ~spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f53,f41,f29,f67])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl3_5 <=> ! [X1,X0] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ~r2_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_5)),
% 0.21/0.49    inference(resolution,[],[f42,f30])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f41])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f63])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f59])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f16,f49])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f19,f45])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f18,f41])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f15,f33])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f14,f29])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    r2_xboole_0(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f13,f25])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    r2_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (23494)------------------------------
% 0.21/0.50  % (23494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23494)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (23494)Memory used [KB]: 10618
% 0.21/0.50  % (23494)Time elapsed: 0.075 s
% 0.21/0.50  % (23494)------------------------------
% 0.21/0.50  % (23494)------------------------------
% 0.21/0.50  % (23499)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (23484)Success in time 0.141 s
%------------------------------------------------------------------------------
