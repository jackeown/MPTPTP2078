%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 151 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :    7
%              Number of atoms          :  197 ( 344 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3019,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f39,f43,f47,f51,f55,f62,f101,f106,f113,f120,f371,f379,f418,f1756,f1939,f2949])).

fof(f2949,plain,
    ( spl4_1
    | ~ spl4_5
    | ~ spl4_160
    | ~ spl4_173 ),
    inference(avatar_contradiction_clause,[],[f2948])).

fof(f2948,plain,
    ( $false
    | spl4_1
    | ~ spl4_5
    | ~ spl4_160
    | ~ spl4_173 ),
    inference(subsumption_resolution,[],[f2947,f24])).

fof(f24,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl4_1
  <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2947,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ spl4_5
    | ~ spl4_160
    | ~ spl4_173 ),
    inference(forward_demodulation,[],[f2902,f42])).

fof(f42,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f2902,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK0),k3_xboole_0(sK1,sK3))
    | ~ spl4_160
    | ~ spl4_173 ),
    inference(superposition,[],[f1755,f1937])).

fof(f1937,plain,
    ( ! [X0] : k3_xboole_0(sK2,X0) = k3_xboole_0(sK2,k3_xboole_0(X0,sK3))
    | ~ spl4_173 ),
    inference(avatar_component_clause,[],[f1936])).

fof(f1936,plain,
    ( spl4_173
  <=> ! [X0] : k3_xboole_0(sK2,X0) = k3_xboole_0(sK2,k3_xboole_0(X0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_173])])).

fof(f1755,plain,
    ( ! [X30,X31] : r1_tarski(k3_xboole_0(X31,k3_xboole_0(sK0,X30)),k3_xboole_0(sK1,X30))
    | ~ spl4_160 ),
    inference(avatar_component_clause,[],[f1754])).

fof(f1754,plain,
    ( spl4_160
  <=> ! [X31,X30] : r1_tarski(k3_xboole_0(X31,k3_xboole_0(sK0,X30)),k3_xboole_0(sK1,X30)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).

fof(f1939,plain,
    ( spl4_173
    | ~ spl4_5
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f1894,f377,f41,f1936])).

fof(f377,plain,
    ( spl4_36
  <=> ! [X32] : k3_xboole_0(sK2,k3_xboole_0(sK3,X32)) = k3_xboole_0(sK2,X32) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f1894,plain,
    ( ! [X1] : k3_xboole_0(sK2,X1) = k3_xboole_0(sK2,k3_xboole_0(X1,sK3))
    | ~ spl4_5
    | ~ spl4_36 ),
    inference(superposition,[],[f378,f42])).

fof(f378,plain,
    ( ! [X32] : k3_xboole_0(sK2,k3_xboole_0(sK3,X32)) = k3_xboole_0(sK2,X32)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f377])).

fof(f1756,plain,
    ( spl4_160
    | ~ spl4_34
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f1711,f416,f369,f1754])).

fof(f369,plain,
    ( spl4_34
  <=> ! [X30] : k3_xboole_0(sK0,k3_xboole_0(sK1,X30)) = k3_xboole_0(sK0,X30) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f416,plain,
    ( spl4_44
  <=> ! [X16,X15,X17] : r1_tarski(k3_xboole_0(X15,k3_xboole_0(X16,X17)),X17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1711,plain,
    ( ! [X30,X31] : r1_tarski(k3_xboole_0(X31,k3_xboole_0(sK0,X30)),k3_xboole_0(sK1,X30))
    | ~ spl4_34
    | ~ spl4_44 ),
    inference(superposition,[],[f417,f370])).

fof(f370,plain,
    ( ! [X30] : k3_xboole_0(sK0,k3_xboole_0(sK1,X30)) = k3_xboole_0(sK0,X30)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f369])).

fof(f417,plain,
    ( ! [X17,X15,X16] : r1_tarski(k3_xboole_0(X15,k3_xboole_0(X16,X17)),X17)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f416])).

fof(f418,plain,
    ( spl4_44
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f327,f59,f53,f416])).

fof(f53,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f59,plain,
    ( spl4_9
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f327,plain,
    ( ! [X17,X15,X16] : r1_tarski(k3_xboole_0(X15,k3_xboole_0(X16,X17)),X17)
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(superposition,[],[f60,f54])).

fof(f54,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f60,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f379,plain,
    ( spl4_36
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f311,f117,f53,f377])).

fof(f117,plain,
    ( spl4_19
  <=> sK2 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f311,plain,
    ( ! [X32] : k3_xboole_0(sK2,k3_xboole_0(sK3,X32)) = k3_xboole_0(sK2,X32)
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(superposition,[],[f54,f119])).

fof(f119,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f117])).

fof(f371,plain,
    ( spl4_34
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f309,f110,f53,f369])).

fof(f110,plain,
    ( spl4_18
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f309,plain,
    ( ! [X30] : k3_xboole_0(sK0,k3_xboole_0(sK1,X30)) = k3_xboole_0(sK0,X30)
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(superposition,[],[f54,f112])).

fof(f112,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f110])).

fof(f120,plain,
    ( spl4_19
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f115,f103,f45,f117])).

fof(f45,plain,
    ( spl4_6
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f103,plain,
    ( spl4_17
  <=> sK3 = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f115,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(superposition,[],[f46,f105])).

fof(f105,plain,
    ( sK3 = k2_xboole_0(sK2,sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f103])).

fof(f46,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f113,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f108,f98,f45,f110])).

fof(f98,plain,
    ( spl4_16
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f108,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(superposition,[],[f46,f100])).

fof(f100,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f98])).

fof(f106,plain,
    ( spl4_17
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f80,f49,f27,f103])).

fof(f27,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f49,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f80,plain,
    ( sK3 = k2_xboole_0(sK2,sK3)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f50,f29])).

fof(f29,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f101,plain,
    ( spl4_16
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f79,f49,f32,f98])).

fof(f32,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f79,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f50,f34])).

fof(f34,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f62,plain,
    ( spl4_9
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f57,f41,f37,f59])).

fof(f37,plain,
    ( spl4_4
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f57,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f38,f42])).

fof(f38,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f55,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f20,f53])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f51,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f47,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f43,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f35,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f13,f32])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

fof(f30,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f15,f22])).

fof(f15,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (22132)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.41  % (22122)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.41  % (22131)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.42  % (22125)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.43  % (22128)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.45  % (22126)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.45  % (22132)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f3019,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f25,f30,f35,f39,f43,f47,f51,f55,f62,f101,f106,f113,f120,f371,f379,f418,f1756,f1939,f2949])).
% 0.20/0.45  fof(f2949,plain,(
% 0.20/0.45    spl4_1 | ~spl4_5 | ~spl4_160 | ~spl4_173),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f2948])).
% 0.20/0.45  fof(f2948,plain,(
% 0.20/0.45    $false | (spl4_1 | ~spl4_5 | ~spl4_160 | ~spl4_173)),
% 0.20/0.45    inference(subsumption_resolution,[],[f2947,f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) | spl4_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    spl4_1 <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.45  fof(f2947,plain,(
% 0.20/0.45    r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) | (~spl4_5 | ~spl4_160 | ~spl4_173)),
% 0.20/0.45    inference(forward_demodulation,[],[f2902,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl4_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    spl4_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.45  fof(f2902,plain,(
% 0.20/0.45    r1_tarski(k3_xboole_0(sK2,sK0),k3_xboole_0(sK1,sK3)) | (~spl4_160 | ~spl4_173)),
% 0.20/0.45    inference(superposition,[],[f1755,f1937])).
% 0.20/0.45  fof(f1937,plain,(
% 0.20/0.45    ( ! [X0] : (k3_xboole_0(sK2,X0) = k3_xboole_0(sK2,k3_xboole_0(X0,sK3))) ) | ~spl4_173),
% 0.20/0.45    inference(avatar_component_clause,[],[f1936])).
% 0.20/0.45  fof(f1936,plain,(
% 0.20/0.45    spl4_173 <=> ! [X0] : k3_xboole_0(sK2,X0) = k3_xboole_0(sK2,k3_xboole_0(X0,sK3))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_173])])).
% 0.20/0.45  fof(f1755,plain,(
% 0.20/0.45    ( ! [X30,X31] : (r1_tarski(k3_xboole_0(X31,k3_xboole_0(sK0,X30)),k3_xboole_0(sK1,X30))) ) | ~spl4_160),
% 0.20/0.45    inference(avatar_component_clause,[],[f1754])).
% 0.20/0.45  fof(f1754,plain,(
% 0.20/0.45    spl4_160 <=> ! [X31,X30] : r1_tarski(k3_xboole_0(X31,k3_xboole_0(sK0,X30)),k3_xboole_0(sK1,X30))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).
% 0.20/0.45  fof(f1939,plain,(
% 0.20/0.45    spl4_173 | ~spl4_5 | ~spl4_36),
% 0.20/0.45    inference(avatar_split_clause,[],[f1894,f377,f41,f1936])).
% 0.20/0.45  fof(f377,plain,(
% 0.20/0.45    spl4_36 <=> ! [X32] : k3_xboole_0(sK2,k3_xboole_0(sK3,X32)) = k3_xboole_0(sK2,X32)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.45  fof(f1894,plain,(
% 0.20/0.45    ( ! [X1] : (k3_xboole_0(sK2,X1) = k3_xboole_0(sK2,k3_xboole_0(X1,sK3))) ) | (~spl4_5 | ~spl4_36)),
% 0.20/0.45    inference(superposition,[],[f378,f42])).
% 0.20/0.45  fof(f378,plain,(
% 0.20/0.45    ( ! [X32] : (k3_xboole_0(sK2,k3_xboole_0(sK3,X32)) = k3_xboole_0(sK2,X32)) ) | ~spl4_36),
% 0.20/0.45    inference(avatar_component_clause,[],[f377])).
% 0.20/0.45  fof(f1756,plain,(
% 0.20/0.45    spl4_160 | ~spl4_34 | ~spl4_44),
% 0.20/0.45    inference(avatar_split_clause,[],[f1711,f416,f369,f1754])).
% 0.20/0.45  fof(f369,plain,(
% 0.20/0.45    spl4_34 <=> ! [X30] : k3_xboole_0(sK0,k3_xboole_0(sK1,X30)) = k3_xboole_0(sK0,X30)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.45  fof(f416,plain,(
% 0.20/0.45    spl4_44 <=> ! [X16,X15,X17] : r1_tarski(k3_xboole_0(X15,k3_xboole_0(X16,X17)),X17)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.20/0.45  fof(f1711,plain,(
% 0.20/0.45    ( ! [X30,X31] : (r1_tarski(k3_xboole_0(X31,k3_xboole_0(sK0,X30)),k3_xboole_0(sK1,X30))) ) | (~spl4_34 | ~spl4_44)),
% 0.20/0.45    inference(superposition,[],[f417,f370])).
% 0.20/0.45  fof(f370,plain,(
% 0.20/0.45    ( ! [X30] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X30)) = k3_xboole_0(sK0,X30)) ) | ~spl4_34),
% 0.20/0.45    inference(avatar_component_clause,[],[f369])).
% 0.20/0.45  fof(f417,plain,(
% 0.20/0.45    ( ! [X17,X15,X16] : (r1_tarski(k3_xboole_0(X15,k3_xboole_0(X16,X17)),X17)) ) | ~spl4_44),
% 0.20/0.45    inference(avatar_component_clause,[],[f416])).
% 0.20/0.45  fof(f418,plain,(
% 0.20/0.45    spl4_44 | ~spl4_8 | ~spl4_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f327,f59,f53,f416])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    spl4_8 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    spl4_9 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.45  fof(f327,plain,(
% 0.20/0.45    ( ! [X17,X15,X16] : (r1_tarski(k3_xboole_0(X15,k3_xboole_0(X16,X17)),X17)) ) | (~spl4_8 | ~spl4_9)),
% 0.20/0.45    inference(superposition,[],[f60,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl4_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f53])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | ~spl4_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f59])).
% 0.20/0.45  fof(f379,plain,(
% 0.20/0.45    spl4_36 | ~spl4_8 | ~spl4_19),
% 0.20/0.45    inference(avatar_split_clause,[],[f311,f117,f53,f377])).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    spl4_19 <=> sK2 = k3_xboole_0(sK2,sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.45  fof(f311,plain,(
% 0.20/0.45    ( ! [X32] : (k3_xboole_0(sK2,k3_xboole_0(sK3,X32)) = k3_xboole_0(sK2,X32)) ) | (~spl4_8 | ~spl4_19)),
% 0.20/0.45    inference(superposition,[],[f54,f119])).
% 0.20/0.45  fof(f119,plain,(
% 0.20/0.45    sK2 = k3_xboole_0(sK2,sK3) | ~spl4_19),
% 0.20/0.45    inference(avatar_component_clause,[],[f117])).
% 0.20/0.45  fof(f371,plain,(
% 0.20/0.45    spl4_34 | ~spl4_8 | ~spl4_18),
% 0.20/0.45    inference(avatar_split_clause,[],[f309,f110,f53,f369])).
% 0.20/0.45  fof(f110,plain,(
% 0.20/0.45    spl4_18 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.45  fof(f309,plain,(
% 0.20/0.45    ( ! [X30] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X30)) = k3_xboole_0(sK0,X30)) ) | (~spl4_8 | ~spl4_18)),
% 0.20/0.45    inference(superposition,[],[f54,f112])).
% 0.20/0.45  fof(f112,plain,(
% 0.20/0.45    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_18),
% 0.20/0.45    inference(avatar_component_clause,[],[f110])).
% 0.20/0.45  fof(f120,plain,(
% 0.20/0.45    spl4_19 | ~spl4_6 | ~spl4_17),
% 0.20/0.45    inference(avatar_split_clause,[],[f115,f103,f45,f117])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    spl4_6 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    spl4_17 <=> sK3 = k2_xboole_0(sK2,sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    sK2 = k3_xboole_0(sK2,sK3) | (~spl4_6 | ~spl4_17)),
% 0.20/0.45    inference(superposition,[],[f46,f105])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    sK3 = k2_xboole_0(sK2,sK3) | ~spl4_17),
% 0.20/0.45    inference(avatar_component_clause,[],[f103])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | ~spl4_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f45])).
% 0.20/0.45  fof(f113,plain,(
% 0.20/0.45    spl4_18 | ~spl4_6 | ~spl4_16),
% 0.20/0.45    inference(avatar_split_clause,[],[f108,f98,f45,f110])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    spl4_16 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.45  fof(f108,plain,(
% 0.20/0.45    sK0 = k3_xboole_0(sK0,sK1) | (~spl4_6 | ~spl4_16)),
% 0.20/0.45    inference(superposition,[],[f46,f100])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    sK1 = k2_xboole_0(sK0,sK1) | ~spl4_16),
% 0.20/0.45    inference(avatar_component_clause,[],[f98])).
% 0.20/0.45  fof(f106,plain,(
% 0.20/0.45    spl4_17 | ~spl4_2 | ~spl4_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f80,f49,f27,f103])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    spl4_7 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    sK3 = k2_xboole_0(sK2,sK3) | (~spl4_2 | ~spl4_7)),
% 0.20/0.45    inference(resolution,[],[f50,f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f27])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f49])).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    spl4_16 | ~spl4_3 | ~spl4_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f79,f49,f32,f98])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    sK1 = k2_xboole_0(sK0,sK1) | (~spl4_3 | ~spl4_7)),
% 0.20/0.45    inference(resolution,[],[f50,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f32])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    spl4_9 | ~spl4_4 | ~spl4_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f57,f41,f37,f59])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    spl4_4 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl4_4 | ~spl4_5)),
% 0.20/0.45    inference(superposition,[],[f38,f42])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl4_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f37])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    spl4_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f20,f53])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    spl4_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f19,f49])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    spl4_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f18,f45])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    spl4_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f17,f41])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    spl4_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f16,f37])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    spl4_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f13,f32])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    r1_tarski(sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.20/0.45    inference(negated_conjecture,[],[f6])).
% 0.20/0.45  fof(f6,conjecture,(
% 0.20/0.45    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f14,f27])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    r1_tarski(sK2,sK3)),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ~spl4_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f15,f22])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (22132)------------------------------
% 0.20/0.45  % (22132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (22132)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (22132)Memory used [KB]: 8059
% 0.20/0.45  % (22132)Time elapsed: 0.044 s
% 0.20/0.45  % (22132)------------------------------
% 0.20/0.45  % (22132)------------------------------
% 0.20/0.45  % (22121)Success in time 0.098 s
%------------------------------------------------------------------------------
