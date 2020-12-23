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
% DateTime   : Thu Dec  3 12:31:00 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 168 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  174 ( 334 expanded)
%              Number of equality atoms :   46 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2625,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f66,f669,f1651,f1847,f2405,f2420,f2572,f2604])).

fof(f2604,plain,
    ( spl5_1
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f2577,f2243,f46])).

fof(f46,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2243,plain,
    ( spl5_39
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f2577,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_39 ),
    inference(superposition,[],[f25,f2245])).

fof(f2245,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f2243])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2572,plain,
    ( spl5_39
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f2571,f2184,f2243])).

fof(f2184,plain,
    ( spl5_37
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f2571,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f2570,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f2570,plain,
    ( k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK0,sK1)
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f2545,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2545,plain,
    ( k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK0)
    | ~ spl5_37 ),
    inference(superposition,[],[f28,f2186])).

fof(f2186,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f2184])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2420,plain,
    ( ~ spl5_4
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f2410,f2188,f63])).

fof(f63,plain,
    ( spl5_4
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2188,plain,
    ( spl5_38
  <=> ! [X5] :
        ( ~ r1_tarski(k4_xboole_0(sK0,sK1),X5)
        | ~ r1_xboole_0(sK2,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f2410,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | ~ spl5_38 ),
    inference(resolution,[],[f2189,f782])).

fof(f782,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(duplicate_literal_removal,[],[f764])).

fof(f764,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X2,X3),X2)
      | r1_tarski(k4_xboole_0(X2,X3),X2) ) ),
    inference(resolution,[],[f98,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f2189,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k4_xboole_0(sK0,sK1),X5)
        | ~ r1_xboole_0(sK2,X5) )
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f2188])).

fof(f2405,plain,
    ( spl5_37
    | spl5_38
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f2404,f1844,f2188,f2184])).

fof(f1844,plain,
    ( spl5_33
  <=> sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f2404,plain,
    ( ! [X40] :
        ( ~ r1_xboole_0(sK2,X40)
        | ~ r1_tarski(k4_xboole_0(sK0,sK1),X40)
        | k1_xboole_0 = k4_xboole_0(sK0,sK1) )
    | ~ spl5_33 ),
    inference(superposition,[],[f171,f1846])).

fof(f1846,plain,
    ( sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f1844])).

fof(f171,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_xboole_0(k2_xboole_0(X6,X4),X5)
      | ~ r1_tarski(X4,X5)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f35,f71])).

fof(f71,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f25,f26])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f1847,plain,
    ( spl5_33
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f1842,f1566,f1844])).

fof(f1566,plain,
    ( spl5_31
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f1842,plain,
    ( sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f1817,f24])).

fof(f1817,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl5_31 ),
    inference(superposition,[],[f125,f1568])).

fof(f1568,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f1566])).

fof(f125,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f28,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1651,plain,
    ( spl5_31
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f1624,f84,f1566])).

fof(f84,plain,
    ( spl5_5
  <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1624,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_5 ),
    inference(superposition,[],[f1286,f86])).

fof(f86,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1286,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f1265,f1147])).

fof(f1147,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f832,f24])).

fof(f832,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6 ),
    inference(resolution,[],[f782,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1265,plain,(
    ! [X2,X1] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f34,f1196])).

fof(f1196,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6) ),
    inference(backward_demodulation,[],[f101,f1147])).

fof(f101,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6) ),
    inference(superposition,[],[f27,f68])).

fof(f68,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f26,f24])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f669,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f667,f56,f84])).

fof(f56,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f667,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f58,f30])).

fof(f58,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f66,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f61,f51,f63])).

fof(f51,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f61,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f29,f53])).

fof(f53,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f59,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f21,f56])).

fof(f21,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f54,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (2185)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (2185)Refutation not found, incomplete strategy% (2185)------------------------------
% 0.21/0.47  % (2185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2201)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.47  % (2185)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (2185)Memory used [KB]: 10618
% 0.21/0.47  % (2185)Time elapsed: 0.050 s
% 0.21/0.47  % (2185)------------------------------
% 0.21/0.47  % (2185)------------------------------
% 0.21/0.54  % (2175)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (2184)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (2184)Refutation not found, incomplete strategy% (2184)------------------------------
% 0.21/0.54  % (2184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2184)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2184)Memory used [KB]: 10618
% 0.21/0.54  % (2184)Time elapsed: 0.126 s
% 0.21/0.54  % (2184)------------------------------
% 0.21/0.54  % (2184)------------------------------
% 0.21/0.54  % (2179)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (2180)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (2175)Refutation not found, incomplete strategy% (2175)------------------------------
% 0.21/0.56  % (2175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2175)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (2175)Memory used [KB]: 1663
% 0.21/0.56  % (2175)Time elapsed: 0.128 s
% 0.21/0.56  % (2175)------------------------------
% 0.21/0.56  % (2175)------------------------------
% 0.21/0.56  % (2202)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (2194)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.56  % (2183)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.57  % (2196)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.57  % (2199)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.57  % (2186)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.57  % (2193)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.57  % (2178)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.57  % (2186)Refutation not found, incomplete strategy% (2186)------------------------------
% 1.35/0.57  % (2186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (2186)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (2186)Memory used [KB]: 10746
% 1.35/0.57  % (2186)Time elapsed: 0.142 s
% 1.35/0.57  % (2186)------------------------------
% 1.35/0.57  % (2186)------------------------------
% 1.35/0.58  % (2197)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.75/0.58  % (2204)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.75/0.58  % (2189)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.75/0.59  % (2192)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.75/0.59  % (2188)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.75/0.59  % (2181)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.75/0.59  % (2177)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.75/0.59  % (2200)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.75/0.60  % (2197)Refutation not found, incomplete strategy% (2197)------------------------------
% 1.75/0.60  % (2197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (2197)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.60  
% 1.75/0.60  % (2197)Memory used [KB]: 10746
% 1.75/0.60  % (2197)Time elapsed: 0.114 s
% 1.75/0.60  % (2197)------------------------------
% 1.75/0.60  % (2197)------------------------------
% 1.75/0.60  % (2182)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.75/0.60  % (2191)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.75/0.60  % (2176)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.75/0.61  % (2192)Refutation not found, incomplete strategy% (2192)------------------------------
% 1.75/0.61  % (2192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.61  % (2192)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.61  
% 1.75/0.61  % (2192)Memory used [KB]: 10618
% 1.75/0.61  % (2192)Time elapsed: 0.200 s
% 1.75/0.61  % (2192)------------------------------
% 1.75/0.61  % (2192)------------------------------
% 1.75/0.62  % (2203)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.75/0.62  % (2187)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.75/0.63  % (2195)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.75/0.63  % (2198)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.75/0.65  % (2190)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.41/0.69  % (2225)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.41/0.69  % (2225)Refutation not found, incomplete strategy% (2225)------------------------------
% 2.41/0.69  % (2225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.41/0.69  % (2225)Termination reason: Refutation not found, incomplete strategy
% 2.41/0.69  
% 2.41/0.69  % (2225)Memory used [KB]: 6140
% 2.41/0.69  % (2225)Time elapsed: 0.168 s
% 2.41/0.69  % (2225)------------------------------
% 2.41/0.69  % (2225)------------------------------
% 2.67/0.72  % (2231)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.76/0.75  % (2230)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.76/0.76  % (2234)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.76/0.78  % (2191)Refutation found. Thanks to Tanya!
% 2.76/0.78  % SZS status Theorem for theBenchmark
% 2.76/0.78  % SZS output start Proof for theBenchmark
% 2.76/0.78  fof(f2625,plain,(
% 2.76/0.78    $false),
% 2.76/0.78    inference(avatar_sat_refutation,[],[f49,f54,f59,f66,f669,f1651,f1847,f2405,f2420,f2572,f2604])).
% 2.76/0.78  fof(f2604,plain,(
% 2.76/0.78    spl5_1 | ~spl5_39),
% 2.76/0.78    inference(avatar_split_clause,[],[f2577,f2243,f46])).
% 2.76/0.78  fof(f46,plain,(
% 2.76/0.78    spl5_1 <=> r1_tarski(sK0,sK1)),
% 2.76/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.76/0.78  fof(f2243,plain,(
% 2.76/0.78    spl5_39 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 2.76/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 2.76/0.78  fof(f2577,plain,(
% 2.76/0.78    r1_tarski(sK0,sK1) | ~spl5_39),
% 2.76/0.78    inference(superposition,[],[f25,f2245])).
% 2.76/0.78  fof(f2245,plain,(
% 2.76/0.78    sK1 = k2_xboole_0(sK0,sK1) | ~spl5_39),
% 2.76/0.78    inference(avatar_component_clause,[],[f2243])).
% 2.76/0.78  fof(f25,plain,(
% 2.76/0.78    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.76/0.78    inference(cnf_transformation,[],[f11])).
% 2.76/0.78  fof(f11,axiom,(
% 2.76/0.78    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.76/0.78  fof(f2572,plain,(
% 2.76/0.78    spl5_39 | ~spl5_37),
% 2.76/0.78    inference(avatar_split_clause,[],[f2571,f2184,f2243])).
% 2.76/0.78  fof(f2184,plain,(
% 2.76/0.78    spl5_37 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 2.76/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.76/0.78  fof(f2571,plain,(
% 2.76/0.78    sK1 = k2_xboole_0(sK0,sK1) | ~spl5_37),
% 2.76/0.78    inference(forward_demodulation,[],[f2570,f24])).
% 2.76/0.78  fof(f24,plain,(
% 2.76/0.78    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.76/0.78    inference(cnf_transformation,[],[f6])).
% 2.76/0.78  fof(f6,axiom,(
% 2.76/0.78    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.76/0.78  fof(f2570,plain,(
% 2.76/0.78    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK0,sK1) | ~spl5_37),
% 2.76/0.78    inference(forward_demodulation,[],[f2545,f26])).
% 2.76/0.78  fof(f26,plain,(
% 2.76/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.76/0.78    inference(cnf_transformation,[],[f1])).
% 2.76/0.78  fof(f1,axiom,(
% 2.76/0.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.76/0.78  fof(f2545,plain,(
% 2.76/0.78    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK0) | ~spl5_37),
% 2.76/0.78    inference(superposition,[],[f28,f2186])).
% 2.76/0.78  fof(f2186,plain,(
% 2.76/0.78    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl5_37),
% 2.76/0.78    inference(avatar_component_clause,[],[f2184])).
% 2.76/0.78  fof(f28,plain,(
% 2.76/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.76/0.78    inference(cnf_transformation,[],[f7])).
% 2.76/0.78  fof(f7,axiom,(
% 2.76/0.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.76/0.78  fof(f2420,plain,(
% 2.76/0.78    ~spl5_4 | ~spl5_38),
% 2.76/0.78    inference(avatar_split_clause,[],[f2410,f2188,f63])).
% 2.76/0.78  fof(f63,plain,(
% 2.76/0.78    spl5_4 <=> r1_xboole_0(sK2,sK0)),
% 2.76/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.76/0.78  fof(f2188,plain,(
% 2.76/0.78    spl5_38 <=> ! [X5] : (~r1_tarski(k4_xboole_0(sK0,sK1),X5) | ~r1_xboole_0(sK2,X5))),
% 2.76/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.76/0.78  fof(f2410,plain,(
% 2.76/0.78    ~r1_xboole_0(sK2,sK0) | ~spl5_38),
% 2.76/0.78    inference(resolution,[],[f2189,f782])).
% 2.76/0.78  fof(f782,plain,(
% 2.76/0.78    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 2.76/0.78    inference(duplicate_literal_removal,[],[f764])).
% 2.76/0.78  fof(f764,plain,(
% 2.76/0.78    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2) | r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 2.76/0.78    inference(resolution,[],[f98,f33])).
% 2.76/0.78  fof(f33,plain,(
% 2.76/0.78    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.76/0.78    inference(cnf_transformation,[],[f18])).
% 2.76/0.78  fof(f18,plain,(
% 2.76/0.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.76/0.78    inference(ennf_transformation,[],[f2])).
% 2.76/0.78  fof(f2,axiom,(
% 2.76/0.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.76/0.78  fof(f98,plain,(
% 2.76/0.78    ( ! [X2,X0,X1] : (r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.76/0.78    inference(resolution,[],[f44,f32])).
% 2.76/0.78  fof(f32,plain,(
% 2.76/0.78    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.76/0.78    inference(cnf_transformation,[],[f18])).
% 2.76/0.78  fof(f44,plain,(
% 2.76/0.78    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 2.76/0.78    inference(equality_resolution,[],[f39])).
% 2.76/0.78  fof(f39,plain,(
% 2.76/0.78    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.76/0.78    inference(cnf_transformation,[],[f3])).
% 2.76/0.78  fof(f3,axiom,(
% 2.76/0.78    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.76/0.78  fof(f2189,plain,(
% 2.76/0.78    ( ! [X5] : (~r1_tarski(k4_xboole_0(sK0,sK1),X5) | ~r1_xboole_0(sK2,X5)) ) | ~spl5_38),
% 2.76/0.78    inference(avatar_component_clause,[],[f2188])).
% 2.76/0.78  fof(f2405,plain,(
% 2.76/0.78    spl5_37 | spl5_38 | ~spl5_33),
% 2.76/0.78    inference(avatar_split_clause,[],[f2404,f1844,f2188,f2184])).
% 2.76/0.78  fof(f1844,plain,(
% 2.76/0.78    spl5_33 <=> sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 2.76/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 2.76/0.78  fof(f2404,plain,(
% 2.76/0.78    ( ! [X40] : (~r1_xboole_0(sK2,X40) | ~r1_tarski(k4_xboole_0(sK0,sK1),X40) | k1_xboole_0 = k4_xboole_0(sK0,sK1)) ) | ~spl5_33),
% 2.76/0.78    inference(superposition,[],[f171,f1846])).
% 2.76/0.78  fof(f1846,plain,(
% 2.76/0.78    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl5_33),
% 2.76/0.78    inference(avatar_component_clause,[],[f1844])).
% 2.76/0.78  fof(f171,plain,(
% 2.76/0.78    ( ! [X6,X4,X5] : (~r1_xboole_0(k2_xboole_0(X6,X4),X5) | ~r1_tarski(X4,X5) | k1_xboole_0 = X4) )),
% 2.76/0.78    inference(resolution,[],[f35,f71])).
% 2.76/0.78  fof(f71,plain,(
% 2.76/0.78    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 2.76/0.78    inference(superposition,[],[f25,f26])).
% 2.76/0.78  fof(f35,plain,(
% 2.76/0.78    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0) )),
% 2.76/0.78    inference(cnf_transformation,[],[f20])).
% 2.76/0.78  fof(f20,plain,(
% 2.76/0.78    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.76/0.78    inference(flattening,[],[f19])).
% 2.76/0.78  fof(f19,plain,(
% 2.76/0.78    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.76/0.78    inference(ennf_transformation,[],[f10])).
% 2.76/0.78  fof(f10,axiom,(
% 2.76/0.78    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 2.76/0.78  fof(f1847,plain,(
% 2.76/0.78    spl5_33 | ~spl5_31),
% 2.76/0.78    inference(avatar_split_clause,[],[f1842,f1566,f1844])).
% 2.76/0.78  fof(f1566,plain,(
% 2.76/0.78    spl5_31 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.76/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.76/0.78  fof(f1842,plain,(
% 2.76/0.78    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl5_31),
% 2.76/0.78    inference(forward_demodulation,[],[f1817,f24])).
% 2.76/0.78  fof(f1817,plain,(
% 2.76/0.78    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl5_31),
% 2.76/0.78    inference(superposition,[],[f125,f1568])).
% 2.76/0.78  fof(f1568,plain,(
% 2.76/0.78    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_31),
% 2.76/0.78    inference(avatar_component_clause,[],[f1566])).
% 2.76/0.78  fof(f125,plain,(
% 2.76/0.78    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 2.76/0.78    inference(superposition,[],[f28,f34])).
% 2.76/0.78  fof(f34,plain,(
% 2.76/0.78    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.76/0.78    inference(cnf_transformation,[],[f9])).
% 2.76/0.78  fof(f9,axiom,(
% 2.76/0.78    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.76/0.78  fof(f1651,plain,(
% 2.76/0.78    spl5_31 | ~spl5_5),
% 2.76/0.78    inference(avatar_split_clause,[],[f1624,f84,f1566])).
% 2.76/0.78  fof(f84,plain,(
% 2.76/0.78    spl5_5 <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.76/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.76/0.78  fof(f1624,plain,(
% 2.76/0.78    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_5),
% 2.76/0.78    inference(superposition,[],[f1286,f86])).
% 2.76/0.78  fof(f86,plain,(
% 2.76/0.78    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_5),
% 2.76/0.78    inference(avatar_component_clause,[],[f84])).
% 2.76/0.78  fof(f1286,plain,(
% 2.76/0.78    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 2.76/0.78    inference(forward_demodulation,[],[f1265,f1147])).
% 2.76/0.78  fof(f1147,plain,(
% 2.76/0.78    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7)) )),
% 2.76/0.78    inference(superposition,[],[f832,f24])).
% 2.76/0.78  fof(f832,plain,(
% 2.76/0.78    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6) )),
% 2.76/0.78    inference(resolution,[],[f782,f30])).
% 2.76/0.78  fof(f30,plain,(
% 2.76/0.78    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.76/0.78    inference(cnf_transformation,[],[f17])).
% 2.76/0.78  fof(f17,plain,(
% 2.76/0.78    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.76/0.78    inference(ennf_transformation,[],[f5])).
% 2.76/0.78  fof(f5,axiom,(
% 2.76/0.78    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.76/0.78  fof(f1265,plain,(
% 2.76/0.78    ( ! [X2,X1] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 2.76/0.78    inference(superposition,[],[f34,f1196])).
% 2.76/0.78  fof(f1196,plain,(
% 2.76/0.78    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,X6)) )),
% 2.76/0.78    inference(backward_demodulation,[],[f101,f1147])).
% 2.76/0.78  fof(f101,plain,(
% 2.76/0.78    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6)) )),
% 2.76/0.78    inference(superposition,[],[f27,f68])).
% 2.76/0.78  fof(f68,plain,(
% 2.76/0.78    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.76/0.78    inference(superposition,[],[f26,f24])).
% 2.76/0.78  fof(f27,plain,(
% 2.76/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.76/0.78    inference(cnf_transformation,[],[f8])).
% 2.76/0.78  fof(f8,axiom,(
% 2.76/0.78    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.76/0.78  fof(f669,plain,(
% 2.76/0.78    spl5_5 | ~spl5_3),
% 2.76/0.78    inference(avatar_split_clause,[],[f667,f56,f84])).
% 2.76/0.78  fof(f56,plain,(
% 2.76/0.78    spl5_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.76/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.76/0.78  fof(f667,plain,(
% 2.76/0.78    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_3),
% 2.76/0.78    inference(resolution,[],[f58,f30])).
% 2.76/0.78  fof(f58,plain,(
% 2.76/0.78    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_3),
% 2.76/0.78    inference(avatar_component_clause,[],[f56])).
% 2.76/0.78  fof(f66,plain,(
% 2.76/0.78    spl5_4 | ~spl5_2),
% 2.76/0.78    inference(avatar_split_clause,[],[f61,f51,f63])).
% 2.76/0.78  fof(f51,plain,(
% 2.76/0.78    spl5_2 <=> r1_xboole_0(sK0,sK2)),
% 2.76/0.78    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.76/0.78  fof(f61,plain,(
% 2.76/0.78    r1_xboole_0(sK2,sK0) | ~spl5_2),
% 2.76/0.78    inference(resolution,[],[f29,f53])).
% 2.76/0.78  fof(f53,plain,(
% 2.76/0.78    r1_xboole_0(sK0,sK2) | ~spl5_2),
% 2.76/0.78    inference(avatar_component_clause,[],[f51])).
% 2.76/0.78  fof(f29,plain,(
% 2.76/0.78    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.76/0.78    inference(cnf_transformation,[],[f16])).
% 2.76/0.78  fof(f16,plain,(
% 2.76/0.78    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.76/0.78    inference(ennf_transformation,[],[f4])).
% 2.76/0.78  fof(f4,axiom,(
% 2.76/0.78    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.76/0.78  fof(f59,plain,(
% 2.76/0.78    spl5_3),
% 2.76/0.78    inference(avatar_split_clause,[],[f21,f56])).
% 2.76/0.78  fof(f21,plain,(
% 2.76/0.78    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.76/0.78    inference(cnf_transformation,[],[f15])).
% 2.76/0.78  fof(f15,plain,(
% 2.76/0.78    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.76/0.78    inference(flattening,[],[f14])).
% 2.76/0.78  fof(f14,plain,(
% 2.76/0.78    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.76/0.78    inference(ennf_transformation,[],[f13])).
% 2.76/0.78  fof(f13,negated_conjecture,(
% 2.76/0.78    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.76/0.78    inference(negated_conjecture,[],[f12])).
% 2.76/0.78  fof(f12,conjecture,(
% 2.76/0.78    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.76/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 2.76/0.78  fof(f54,plain,(
% 2.76/0.78    spl5_2),
% 2.76/0.78    inference(avatar_split_clause,[],[f22,f51])).
% 2.76/0.78  fof(f22,plain,(
% 2.76/0.78    r1_xboole_0(sK0,sK2)),
% 2.76/0.78    inference(cnf_transformation,[],[f15])).
% 2.76/0.78  fof(f49,plain,(
% 2.76/0.78    ~spl5_1),
% 2.76/0.78    inference(avatar_split_clause,[],[f23,f46])).
% 2.76/0.78  fof(f23,plain,(
% 2.76/0.78    ~r1_tarski(sK0,sK1)),
% 2.76/0.78    inference(cnf_transformation,[],[f15])).
% 2.76/0.78  % SZS output end Proof for theBenchmark
% 2.76/0.78  % (2191)------------------------------
% 2.76/0.78  % (2191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.78  % (2191)Termination reason: Refutation
% 2.76/0.78  
% 2.76/0.78  % (2191)Memory used [KB]: 12792
% 2.76/0.78  % (2191)Time elapsed: 0.371 s
% 2.76/0.78  % (2191)------------------------------
% 2.76/0.78  % (2191)------------------------------
% 2.76/0.78  % (2174)Success in time 0.415 s
%------------------------------------------------------------------------------
