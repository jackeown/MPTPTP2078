%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:37 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 123 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :  188 ( 318 expanded)
%              Number of equality atoms :   40 (  80 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f37,f55,f59,f75,f91,f98,f105,f128,f156,f196,f232])).

fof(f232,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f210,f194,f53,f23,f96])).

fof(f96,plain,
    ( spl3_15
  <=> k1_xboole_0 = k2_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f23,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK2(X0,X1,X2),X1)
        | ~ r2_hidden(sK2(X0,X1,X2),X2)
        | k2_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f194,plain,
    ( spl3_22
  <=> ! [X1] : r2_hidden(sK2(sK0,sK1,sK1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f210,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f24,f209])).

fof(f209,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f208,f24])).

fof(f208,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f201,f195])).

fof(f195,plain,
    ( ! [X1] : r2_hidden(sK2(sK0,sK1,sK1),X1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f201,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(resolution,[],[f195,f54])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK2(X0,X1,X2),X2)
        | ~ r2_hidden(sK2(X0,X1,X2),X1)
        | k2_xboole_0(X0,X1) = X2 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f53])).

fof(f24,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f196,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f170,f154,f31,f27,f194])).

fof(f27,plain,
    ( spl3_3
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f31,plain,
    ( spl3_4
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f154,plain,
    ( spl3_20
  <=> r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f170,plain,
    ( ! [X1] : r2_hidden(sK2(sK0,sK1,sK1),X1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f169,f28])).

fof(f28,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f169,plain,
    ( ! [X1] : r2_hidden(sK2(sK0,sK1,sK1),k2_xboole_0(X1,k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(resolution,[],[f155,f32])).

fof(f32,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X1)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f155,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f154])).

fof(f156,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f136,f126,f23,f154])).

fof(f126,plain,
    ( spl3_17
  <=> ! [X0] : r2_hidden(sK2(sK0,sK1,sK1),k2_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f136,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(superposition,[],[f127,f24])).

fof(f127,plain,
    ( ! [X0] : r2_hidden(sK2(sK0,sK1,sK1),k2_xboole_0(sK0,X0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( spl3_17
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f110,f86,f35,f126])).

fof(f35,plain,
    ( spl3_5
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f86,plain,
    ( spl3_13
  <=> r2_hidden(sK2(sK0,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f110,plain,
    ( ! [X0] : r2_hidden(sK2(sK0,sK1,sK1),k2_xboole_0(sK0,X0))
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(resolution,[],[f87,f36])).

fof(f36,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f87,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f105,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f100,f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    | spl3_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f100,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(superposition,[],[f28,f97])).

fof(f97,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f94,f89,f23,f96])).

fof(f89,plain,
    ( spl3_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f94,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f24,f90])).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,
    ( spl3_13
    | spl3_14
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f80,f73,f23,f89,f86])).

fof(f73,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f80,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(sK2(sK0,sK1,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(superposition,[],[f74,f24])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | r2_hidden(sK2(X0,X1,X1),X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f75,plain,
    ( spl3_11
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f70,f57,f53,f73])).

fof(f57,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK2(X0,X1,X2),X0)
        | r2_hidden(sK2(X0,X1,X2),X1)
        | r2_hidden(sK2(X0,X1,X2),X2)
        | k2_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f66,f54])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1,X1),X1)
        | r2_hidden(sK2(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_10 ),
    inference(factoring,[],[f58])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X2)
        | r2_hidden(sK2(X0,X1,X2),X1)
        | r2_hidden(sK2(X0,X1,X2),X0)
        | k2_xboole_0(X0,X1) = X2 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f11,f57])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f55,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f10,f53])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f37,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f29,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f8,f27])).

fof(f8,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f25,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f6,f23])).

fof(f6,plain,(
    k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & k2_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = k1_xboole_0
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f21,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f7,f19])).

fof(f7,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : run_vampire %s %d
% 0.10/0.30  % Computer   : n013.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 09:32:24 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.15/0.42  % (14140)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.15/0.42  % (14137)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.15/0.42  % (14144)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.15/0.42  % (14136)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.15/0.43  % (14135)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.15/0.43  % (14132)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.15/0.43  % (14132)Refutation not found, incomplete strategy% (14132)------------------------------
% 0.15/0.43  % (14132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.43  % (14132)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.43  
% 0.15/0.43  % (14132)Memory used [KB]: 10618
% 0.15/0.43  % (14132)Time elapsed: 0.075 s
% 0.15/0.43  % (14132)------------------------------
% 0.15/0.43  % (14132)------------------------------
% 0.15/0.44  % (14140)Refutation found. Thanks to Tanya!
% 0.15/0.44  % SZS status Theorem for theBenchmark
% 0.15/0.44  % SZS output start Proof for theBenchmark
% 0.15/0.44  fof(f233,plain,(
% 0.15/0.44    $false),
% 0.15/0.44    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f37,f55,f59,f75,f91,f98,f105,f128,f156,f196,f232])).
% 0.15/0.44  fof(f232,plain,(
% 0.15/0.44    spl3_15 | ~spl3_2 | ~spl3_9 | ~spl3_22),
% 0.15/0.44    inference(avatar_split_clause,[],[f210,f194,f53,f23,f96])).
% 0.15/0.44  fof(f96,plain,(
% 0.15/0.44    spl3_15 <=> k1_xboole_0 = k2_xboole_0(sK0,k1_xboole_0)),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.15/0.44  fof(f23,plain,(
% 0.15/0.44    spl3_2 <=> k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.15/0.44  fof(f53,plain,(
% 0.15/0.44    spl3_9 <=> ! [X1,X0,X2] : (~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2)),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.15/0.44  fof(f194,plain,(
% 0.15/0.44    spl3_22 <=> ! [X1] : r2_hidden(sK2(sK0,sK1,sK1),X1)),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.15/0.44  fof(f210,plain,(
% 0.15/0.44    k1_xboole_0 = k2_xboole_0(sK0,k1_xboole_0) | (~spl3_2 | ~spl3_9 | ~spl3_22)),
% 0.15/0.44    inference(backward_demodulation,[],[f24,f209])).
% 0.15/0.44  fof(f209,plain,(
% 0.15/0.44    k1_xboole_0 = sK1 | (~spl3_2 | ~spl3_9 | ~spl3_22)),
% 0.15/0.44    inference(forward_demodulation,[],[f208,f24])).
% 0.15/0.44  fof(f208,plain,(
% 0.15/0.44    sK1 = k2_xboole_0(sK0,sK1) | (~spl3_9 | ~spl3_22)),
% 0.15/0.44    inference(subsumption_resolution,[],[f201,f195])).
% 0.15/0.44  fof(f195,plain,(
% 0.15/0.44    ( ! [X1] : (r2_hidden(sK2(sK0,sK1,sK1),X1)) ) | ~spl3_22),
% 0.15/0.44    inference(avatar_component_clause,[],[f194])).
% 0.15/0.44  fof(f201,plain,(
% 0.15/0.44    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | sK1 = k2_xboole_0(sK0,sK1) | (~spl3_9 | ~spl3_22)),
% 0.15/0.44    inference(resolution,[],[f195,f54])).
% 0.15/0.44  fof(f54,plain,(
% 0.15/0.44    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) ) | ~spl3_9),
% 0.15/0.44    inference(avatar_component_clause,[],[f53])).
% 0.15/0.44  fof(f24,plain,(
% 0.15/0.44    k1_xboole_0 = k2_xboole_0(sK0,sK1) | ~spl3_2),
% 0.15/0.44    inference(avatar_component_clause,[],[f23])).
% 0.15/0.44  fof(f196,plain,(
% 0.15/0.44    spl3_22 | ~spl3_3 | ~spl3_4 | ~spl3_20),
% 0.15/0.44    inference(avatar_split_clause,[],[f170,f154,f31,f27,f194])).
% 0.15/0.44  fof(f27,plain,(
% 0.15/0.44    spl3_3 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.15/0.44  fof(f31,plain,(
% 0.15/0.44    spl3_4 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1)))),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.15/0.44  fof(f154,plain,(
% 0.15/0.44    spl3_20 <=> r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0)),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.15/0.44  fof(f170,plain,(
% 0.15/0.44    ( ! [X1] : (r2_hidden(sK2(sK0,sK1,sK1),X1)) ) | (~spl3_3 | ~spl3_4 | ~spl3_20)),
% 0.15/0.44    inference(forward_demodulation,[],[f169,f28])).
% 0.15/0.44  fof(f28,plain,(
% 0.15/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.15/0.44    inference(avatar_component_clause,[],[f27])).
% 0.15/0.44  fof(f169,plain,(
% 0.15/0.44    ( ! [X1] : (r2_hidden(sK2(sK0,sK1,sK1),k2_xboole_0(X1,k1_xboole_0))) ) | (~spl3_4 | ~spl3_20)),
% 0.15/0.44    inference(resolution,[],[f155,f32])).
% 0.15/0.44  fof(f32,plain,(
% 0.15/0.44    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) ) | ~spl3_4),
% 0.15/0.44    inference(avatar_component_clause,[],[f31])).
% 0.15/0.44  fof(f155,plain,(
% 0.15/0.44    r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) | ~spl3_20),
% 0.15/0.44    inference(avatar_component_clause,[],[f154])).
% 0.15/0.44  fof(f156,plain,(
% 0.15/0.44    spl3_20 | ~spl3_2 | ~spl3_17),
% 0.15/0.44    inference(avatar_split_clause,[],[f136,f126,f23,f154])).
% 0.15/0.44  fof(f126,plain,(
% 0.15/0.44    spl3_17 <=> ! [X0] : r2_hidden(sK2(sK0,sK1,sK1),k2_xboole_0(sK0,X0))),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.15/0.44  fof(f136,plain,(
% 0.15/0.44    r2_hidden(sK2(sK0,sK1,sK1),k1_xboole_0) | (~spl3_2 | ~spl3_17)),
% 0.15/0.44    inference(superposition,[],[f127,f24])).
% 0.15/0.44  fof(f127,plain,(
% 0.15/0.44    ( ! [X0] : (r2_hidden(sK2(sK0,sK1,sK1),k2_xboole_0(sK0,X0))) ) | ~spl3_17),
% 0.15/0.44    inference(avatar_component_clause,[],[f126])).
% 0.15/0.44  fof(f128,plain,(
% 0.15/0.44    spl3_17 | ~spl3_5 | ~spl3_13),
% 0.15/0.44    inference(avatar_split_clause,[],[f110,f86,f35,f126])).
% 0.15/0.44  fof(f35,plain,(
% 0.15/0.44    spl3_5 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1)))),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.15/0.44  fof(f86,plain,(
% 0.15/0.44    spl3_13 <=> r2_hidden(sK2(sK0,sK1,sK1),sK0)),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.15/0.44  fof(f110,plain,(
% 0.15/0.44    ( ! [X0] : (r2_hidden(sK2(sK0,sK1,sK1),k2_xboole_0(sK0,X0))) ) | (~spl3_5 | ~spl3_13)),
% 0.15/0.44    inference(resolution,[],[f87,f36])).
% 0.15/0.44  fof(f36,plain,(
% 0.15/0.44    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) ) | ~spl3_5),
% 0.15/0.44    inference(avatar_component_clause,[],[f35])).
% 0.15/0.44  fof(f87,plain,(
% 0.15/0.44    r2_hidden(sK2(sK0,sK1,sK1),sK0) | ~spl3_13),
% 0.15/0.44    inference(avatar_component_clause,[],[f86])).
% 0.15/0.44  fof(f105,plain,(
% 0.15/0.44    spl3_1 | ~spl3_3 | ~spl3_15),
% 0.15/0.44    inference(avatar_contradiction_clause,[],[f104])).
% 0.15/0.44  fof(f104,plain,(
% 0.15/0.44    $false | (spl3_1 | ~spl3_3 | ~spl3_15)),
% 0.15/0.44    inference(subsumption_resolution,[],[f100,f20])).
% 0.15/0.44  fof(f20,plain,(
% 0.15/0.44    k1_xboole_0 != sK0 | spl3_1),
% 0.15/0.44    inference(avatar_component_clause,[],[f19])).
% 0.15/0.44  fof(f19,plain,(
% 0.15/0.44    spl3_1 <=> k1_xboole_0 = sK0),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.15/0.44  fof(f100,plain,(
% 0.15/0.44    k1_xboole_0 = sK0 | (~spl3_3 | ~spl3_15)),
% 0.15/0.44    inference(superposition,[],[f28,f97])).
% 0.15/0.44  fof(f97,plain,(
% 0.15/0.44    k1_xboole_0 = k2_xboole_0(sK0,k1_xboole_0) | ~spl3_15),
% 0.15/0.44    inference(avatar_component_clause,[],[f96])).
% 0.15/0.44  fof(f98,plain,(
% 0.15/0.44    spl3_15 | ~spl3_2 | ~spl3_14),
% 0.15/0.44    inference(avatar_split_clause,[],[f94,f89,f23,f96])).
% 0.15/0.44  fof(f89,plain,(
% 0.15/0.44    spl3_14 <=> k1_xboole_0 = sK1),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.15/0.44  fof(f94,plain,(
% 0.15/0.44    k1_xboole_0 = k2_xboole_0(sK0,k1_xboole_0) | (~spl3_2 | ~spl3_14)),
% 0.15/0.44    inference(backward_demodulation,[],[f24,f90])).
% 0.15/0.44  fof(f90,plain,(
% 0.15/0.44    k1_xboole_0 = sK1 | ~spl3_14),
% 0.15/0.44    inference(avatar_component_clause,[],[f89])).
% 0.15/0.44  fof(f91,plain,(
% 0.15/0.44    spl3_13 | spl3_14 | ~spl3_2 | ~spl3_11),
% 0.15/0.44    inference(avatar_split_clause,[],[f80,f73,f23,f89,f86])).
% 0.15/0.44  fof(f73,plain,(
% 0.15/0.44    spl3_11 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1)),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.15/0.44  fof(f80,plain,(
% 0.15/0.44    k1_xboole_0 = sK1 | r2_hidden(sK2(sK0,sK1,sK1),sK0) | (~spl3_2 | ~spl3_11)),
% 0.15/0.44    inference(superposition,[],[f74,f24])).
% 0.15/0.44  fof(f74,plain,(
% 0.15/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | r2_hidden(sK2(X0,X1,X1),X0)) ) | ~spl3_11),
% 0.15/0.44    inference(avatar_component_clause,[],[f73])).
% 0.15/0.44  fof(f75,plain,(
% 0.15/0.44    spl3_11 | ~spl3_9 | ~spl3_10),
% 0.15/0.44    inference(avatar_split_clause,[],[f70,f57,f53,f73])).
% 0.15/0.44  fof(f57,plain,(
% 0.15/0.44    spl3_10 <=> ! [X1,X0,X2] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2)),
% 0.15/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.15/0.44  fof(f70,plain,(
% 0.15/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | (~spl3_9 | ~spl3_10)),
% 0.15/0.44    inference(subsumption_resolution,[],[f66,f54])).
% 0.15/0.44  fof(f66,plain,(
% 0.15/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X1),X1) | r2_hidden(sK2(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_10),
% 0.15/0.44    inference(factoring,[],[f58])).
% 0.15/0.44  fof(f58,plain,(
% 0.15/0.44    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) ) | ~spl3_10),
% 0.15/0.44    inference(avatar_component_clause,[],[f57])).
% 0.15/0.44  fof(f59,plain,(
% 0.15/0.44    spl3_10),
% 0.15/0.44    inference(avatar_split_clause,[],[f11,f57])).
% 0.15/0.44  fof(f11,plain,(
% 0.15/0.44    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.15/0.44    inference(cnf_transformation,[],[f1])).
% 0.15/0.44  fof(f1,axiom,(
% 0.15/0.44    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.15/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.15/0.44  fof(f55,plain,(
% 0.15/0.44    spl3_9),
% 0.15/0.44    inference(avatar_split_clause,[],[f10,f53])).
% 0.15/0.44  fof(f10,plain,(
% 0.15/0.44    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.15/0.44    inference(cnf_transformation,[],[f1])).
% 0.15/0.44  fof(f37,plain,(
% 0.15/0.44    spl3_5),
% 0.15/0.44    inference(avatar_split_clause,[],[f16,f35])).
% 0.15/0.44  fof(f16,plain,(
% 0.15/0.44    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.15/0.44    inference(equality_resolution,[],[f13])).
% 0.15/0.44  fof(f13,plain,(
% 0.15/0.44    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.15/0.44    inference(cnf_transformation,[],[f1])).
% 0.15/0.44  fof(f33,plain,(
% 0.15/0.44    spl3_4),
% 0.15/0.44    inference(avatar_split_clause,[],[f15,f31])).
% 0.15/0.44  fof(f15,plain,(
% 0.15/0.44    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.15/0.44    inference(equality_resolution,[],[f14])).
% 0.15/0.44  fof(f14,plain,(
% 0.15/0.44    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.15/0.44    inference(cnf_transformation,[],[f1])).
% 0.15/0.44  fof(f29,plain,(
% 0.15/0.44    spl3_3),
% 0.15/0.44    inference(avatar_split_clause,[],[f8,f27])).
% 0.15/0.44  fof(f8,plain,(
% 0.15/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.15/0.44    inference(cnf_transformation,[],[f2])).
% 0.15/0.44  fof(f2,axiom,(
% 0.15/0.44    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.15/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.15/0.44  fof(f25,plain,(
% 0.15/0.44    spl3_2),
% 0.15/0.44    inference(avatar_split_clause,[],[f6,f23])).
% 0.15/0.44  fof(f6,plain,(
% 0.15/0.44    k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 0.15/0.44    inference(cnf_transformation,[],[f5])).
% 0.15/0.44  fof(f5,plain,(
% 0.15/0.44    ? [X0,X1] : (k1_xboole_0 != X0 & k2_xboole_0(X0,X1) = k1_xboole_0)),
% 0.15/0.44    inference(ennf_transformation,[],[f4])).
% 0.15/0.44  fof(f4,negated_conjecture,(
% 0.15/0.44    ~! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.15/0.44    inference(negated_conjecture,[],[f3])).
% 0.15/0.44  fof(f3,conjecture,(
% 0.15/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.15/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.15/0.44  fof(f21,plain,(
% 0.15/0.44    ~spl3_1),
% 0.15/0.44    inference(avatar_split_clause,[],[f7,f19])).
% 0.15/0.44  fof(f7,plain,(
% 0.15/0.44    k1_xboole_0 != sK0),
% 0.15/0.44    inference(cnf_transformation,[],[f5])).
% 0.15/0.44  % SZS output end Proof for theBenchmark
% 0.15/0.44  % (14140)------------------------------
% 0.15/0.44  % (14140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.44  % (14140)Termination reason: Refutation
% 0.15/0.44  
% 0.15/0.44  % (14140)Memory used [KB]: 10746
% 0.15/0.44  % (14140)Time elapsed: 0.086 s
% 0.15/0.44  % (14140)------------------------------
% 0.15/0.44  % (14140)------------------------------
% 0.15/0.44  % (14130)Success in time 0.122 s
%------------------------------------------------------------------------------
