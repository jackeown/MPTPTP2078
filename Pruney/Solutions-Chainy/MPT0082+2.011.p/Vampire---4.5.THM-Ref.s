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
% DateTime   : Thu Dec  3 12:31:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 156 expanded)
%              Number of leaves         :   27 (  77 expanded)
%              Depth                    :    6
%              Number of atoms          :  202 ( 338 expanded)
%              Number of equality atoms :   58 ( 110 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f649,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f35,f39,f43,f47,f51,f55,f68,f82,f90,f103,f121,f133,f145,f531,f539,f602,f607,f647])).

fof(f647,plain,
    ( spl2_10
    | ~ spl2_16
    | ~ spl2_39 ),
    inference(avatar_contradiction_clause,[],[f646])).

fof(f646,plain,
    ( $false
    | spl2_10
    | ~ spl2_16
    | ~ spl2_39 ),
    inference(subsumption_resolution,[],[f81,f636])).

fof(f636,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl2_16
    | ~ spl2_39 ),
    inference(superposition,[],[f132,f606])).

fof(f606,plain,
    ( ! [X2] : k3_xboole_0(X2,X2) = X2
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f605])).

fof(f605,plain,
    ( spl2_39
  <=> ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f132,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f81,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_10
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f607,plain,
    ( spl2_39
    | ~ spl2_34
    | ~ spl2_36
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f603,f600,f537,f529,f605])).

fof(f529,plain,
    ( spl2_34
  <=> ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f537,plain,
    ( spl2_36
  <=> ! [X2] : k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f600,plain,
    ( spl2_38
  <=> ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f603,plain,
    ( ! [X2] : k3_xboole_0(X2,X2) = X2
    | ~ spl2_34
    | ~ spl2_36
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f601,f543])).

fof(f543,plain,
    ( ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_34
    | ~ spl2_36 ),
    inference(superposition,[],[f538,f530])).

fof(f530,plain,
    ( ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f529])).

fof(f538,plain,
    ( ! [X2] : k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0) = X2
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f537])).

fof(f601,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f600])).

fof(f602,plain,
    ( spl2_38
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f135,f119,f101,f600])).

fof(f101,plain,
    ( spl2_12
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f119,plain,
    ( spl2_14
  <=> ! [X1,X0] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f135,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(superposition,[],[f120,f102])).

fof(f102,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f120,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f539,plain,
    ( spl2_36
    | ~ spl2_12
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f156,f143,f119,f101,f537])).

fof(f143,plain,
    ( spl2_17
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f156,plain,
    ( ! [X2] : k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0) = X2
    | ~ spl2_12
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f151,f135])).

fof(f151,plain,
    ( ! [X2] : k2_xboole_0(k3_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)),k1_xboole_0) = X2
    | ~ spl2_12
    | ~ spl2_17 ),
    inference(superposition,[],[f144,f102])).

fof(f144,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f143])).

fof(f531,plain,
    ( spl2_34
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f109,f101,f37,f529])).

fof(f37,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f109,plain,
    ( ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(superposition,[],[f38,f102])).

fof(f38,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f145,plain,
    ( spl2_17
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f64,f53,f49,f143])).

fof(f49,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f53,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f64,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(superposition,[],[f54,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f54,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f133,plain,
    ( spl2_16
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f93,f87,f66,f130])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f87,plain,
    ( spl2_11
  <=> k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f93,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1))
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(superposition,[],[f89,f67])).

fof(f67,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f89,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f121,plain,
    ( spl2_14
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f62,f49,f119])).

fof(f62,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_7 ),
    inference(superposition,[],[f50,f50])).

fof(f103,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f57,f41,f33,f101])).

fof(f33,plain,
    ( spl2_3
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f41,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f57,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f34,f42])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f34,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f90,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f56,f41,f28,f87])).

fof(f28,plain,
    ( spl2_2
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f56,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f30,f42])).

fof(f30,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f82,plain,
    ( ~ spl2_10
    | spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f60,f45,f23,f79])).

fof(f23,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f45,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f60,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl2_1
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f25,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f25,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f21,f66])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f55,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f18,f53])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f51,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f17,f49])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f43,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f35,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f31,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f26,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f13,f23])).

fof(f13,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (4175)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (4169)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (4167)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (4179)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (4164)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (4168)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (4171)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (4175)Refutation not found, incomplete strategy% (4175)------------------------------
% 0.21/0.48  % (4175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4175)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4175)Memory used [KB]: 10618
% 0.21/0.48  % (4175)Time elapsed: 0.072 s
% 0.21/0.48  % (4175)------------------------------
% 0.21/0.48  % (4175)------------------------------
% 0.21/0.48  % (4169)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (4178)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (4170)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (4177)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (4166)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (4181)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (4174)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f649,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f26,f31,f35,f39,f43,f47,f51,f55,f68,f82,f90,f103,f121,f133,f145,f531,f539,f602,f607,f647])).
% 0.21/0.48  fof(f647,plain,(
% 0.21/0.48    spl2_10 | ~spl2_16 | ~spl2_39),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f646])).
% 0.21/0.48  fof(f646,plain,(
% 0.21/0.48    $false | (spl2_10 | ~spl2_16 | ~spl2_39)),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f636])).
% 0.21/0.48  fof(f636,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl2_16 | ~spl2_39)),
% 0.21/0.48    inference(superposition,[],[f132,f606])).
% 0.21/0.48  fof(f606,plain,(
% 0.21/0.48    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) ) | ~spl2_39),
% 0.21/0.48    inference(avatar_component_clause,[],[f605])).
% 0.21/0.48  fof(f605,plain,(
% 0.21/0.48    spl2_39 <=> ! [X2] : k3_xboole_0(X2,X2) = X2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)) | ~spl2_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    spl2_16 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl2_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl2_10 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f607,plain,(
% 0.21/0.48    spl2_39 | ~spl2_34 | ~spl2_36 | ~spl2_38),
% 0.21/0.48    inference(avatar_split_clause,[],[f603,f600,f537,f529,f605])).
% 0.21/0.48  fof(f529,plain,(
% 0.21/0.48    spl2_34 <=> ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.48  fof(f537,plain,(
% 0.21/0.48    spl2_36 <=> ! [X2] : k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0) = X2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.48  fof(f600,plain,(
% 0.21/0.48    spl2_38 <=> ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.21/0.48  fof(f603,plain,(
% 0.21/0.48    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) ) | (~spl2_34 | ~spl2_36 | ~spl2_38)),
% 0.21/0.48    inference(forward_demodulation,[],[f601,f543])).
% 0.21/0.48  fof(f543,plain,(
% 0.21/0.48    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl2_34 | ~spl2_36)),
% 0.21/0.48    inference(superposition,[],[f538,f530])).
% 0.21/0.48  fof(f530,plain,(
% 0.21/0.48    ( ! [X5] : (k2_xboole_0(X5,k1_xboole_0) = X5) ) | ~spl2_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f529])).
% 0.21/0.48  fof(f538,plain,(
% 0.21/0.48    ( ! [X2] : (k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0) = X2) ) | ~spl2_36),
% 0.21/0.48    inference(avatar_component_clause,[],[f537])).
% 0.21/0.48  fof(f601,plain,(
% 0.21/0.48    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) ) | ~spl2_38),
% 0.21/0.48    inference(avatar_component_clause,[],[f600])).
% 0.21/0.48  fof(f602,plain,(
% 0.21/0.48    spl2_38 | ~spl2_12 | ~spl2_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f135,f119,f101,f600])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl2_12 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl2_14 <=> ! [X1,X0] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) ) | (~spl2_12 | ~spl2_14)),
% 0.21/0.48    inference(superposition,[],[f120,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl2_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f119])).
% 0.21/0.48  fof(f539,plain,(
% 0.21/0.48    spl2_36 | ~spl2_12 | ~spl2_14 | ~spl2_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f156,f143,f119,f101,f537])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl2_17 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ( ! [X2] : (k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0) = X2) ) | (~spl2_12 | ~spl2_14 | ~spl2_17)),
% 0.21/0.48    inference(forward_demodulation,[],[f151,f135])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X2] : (k2_xboole_0(k3_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)),k1_xboole_0) = X2) ) | (~spl2_12 | ~spl2_17)),
% 0.21/0.48    inference(superposition,[],[f144,f102])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0) ) | ~spl2_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f143])).
% 0.21/0.48  fof(f531,plain,(
% 0.21/0.48    spl2_34 | ~spl2_4 | ~spl2_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f109,f101,f37,f529])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl2_4 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X5] : (k2_xboole_0(X5,k1_xboole_0) = X5) ) | (~spl2_4 | ~spl2_12)),
% 0.21/0.48    inference(superposition,[],[f38,f102])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    spl2_17 | ~spl2_7 | ~spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f64,f53,f49,f143])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl2_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl2_8 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0) ) | (~spl2_7 | ~spl2_8)),
% 0.21/0.48    inference(superposition,[],[f54,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f53])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    spl2_16 | ~spl2_9 | ~spl2_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f93,f87,f66,f130])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl2_9 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl2_11 <=> k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)) | (~spl2_9 | ~spl2_11)),
% 0.21/0.48    inference(superposition,[],[f89,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl2_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK1) | ~spl2_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl2_14 | ~spl2_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f62,f49,f119])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_7),
% 0.21/0.48    inference(superposition,[],[f50,f50])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl2_12 | ~spl2_3 | ~spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f57,f41,f33,f101])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    spl2_3 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl2_5 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl2_3 | ~spl2_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f34,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f41])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f33])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl2_11 | ~spl2_2 | ~spl2_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f41,f28,f87])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    spl2_2 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK1) | (~spl2_2 | ~spl2_5)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f30,f42])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f28])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~spl2_10 | spl2_1 | ~spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f45,f23,f79])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl2_6 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    k1_xboole_0 != k3_xboole_0(sK0,sK1) | (spl2_1 | ~spl2_6)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f25,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f23])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl2_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f66])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl2_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f53])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f17,f49])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f45])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl2_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f41])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f37])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f33])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f28])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ~spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f13,f23])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (4169)------------------------------
% 0.21/0.49  % (4169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4169)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (4169)Memory used [KB]: 6524
% 0.21/0.49  % (4169)Time elapsed: 0.074 s
% 0.21/0.49  % (4169)------------------------------
% 0.21/0.49  % (4169)------------------------------
% 0.21/0.49  % (4161)Success in time 0.13 s
%------------------------------------------------------------------------------
