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
% DateTime   : Thu Dec  3 12:32:32 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 139 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  170 ( 271 expanded)
%              Number of equality atoms :   30 (  62 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f185,f190,f240,f376,f754,f1018,f1206])).

fof(f1206,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1205])).

fof(f1205,plain,
    ( $false
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f1194,f375])).

fof(f375,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl4_7
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

% (21473)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f1194,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f614,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f34,f32])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f614,plain,
    ( ! [X14] :
        ( ~ r1_tarski(X14,sK2)
        | r1_xboole_0(X14,sK0) )
    | ~ spl4_6 ),
    inference(superposition,[],[f169,f239])).

fof(f239,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl4_6
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f169,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_xboole_0(X6,k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5))))
      | ~ r1_tarski(X6,X5) ) ),
    inference(superposition,[],[f55,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f44,f38,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f38])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f1018,plain,
    ( spl4_5
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f1017])).

fof(f1017,plain,
    ( $false
    | spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f1016,f189])).

fof(f189,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl4_5
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1016,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f1011,f347])).

fof(f347,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f84,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1011,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ spl4_8 ),
    inference(resolution,[],[f753,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f753,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f751])).

% (21477)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f751,plain,
    ( spl4_8
  <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f754,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f511,f237,f751])).

fof(f511,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl4_6 ),
    inference(superposition,[],[f171,f239])).

fof(f171,plain,(
    ! [X12,X10,X11] : r1_tarski(k3_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X11,X12))),k3_xboole_0(X10,X11)) ),
    inference(superposition,[],[f50,f54])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f376,plain,
    ( ~ spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f330,f182,f373])).

fof(f182,plain,
    ( spl4_4
  <=> r2_hidden(sK3(sK0,sK2),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f330,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f184,f81])).

fof(f81,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X3,X2))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f40,f36])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f184,plain,
    ( r2_hidden(sK3(sK0,sK2),k3_xboole_0(sK0,sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f182])).

fof(f240,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f86,f66,f237])).

fof(f66,plain,
    ( spl4_3
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f86,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f68,f41])).

fof(f68,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f190,plain,
    ( ~ spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f127,f57,f187])).

fof(f57,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f127,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f59,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f185,plain,
    ( spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f104,f61,f182])).

fof(f61,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f104,plain,
    ( r2_hidden(sK3(sK0,sK2),k3_xboole_0(sK0,sK2))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f69,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f49,f66])).

fof(f49,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f29,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f64,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f30,f61,f57])).

fof(f30,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:49:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (21483)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (21480)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (21486)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (21484)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (21474)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (21476)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (21481)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (21472)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (21475)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (21471)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (21478)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (21485)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (21488)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.34/0.53  % (21487)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.34/0.53  % (21486)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f1207,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(avatar_sat_refutation,[],[f64,f69,f185,f190,f240,f376,f754,f1018,f1206])).
% 1.34/0.53  fof(f1206,plain,(
% 1.34/0.53    ~spl4_6 | spl4_7),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f1205])).
% 1.34/0.53  fof(f1205,plain,(
% 1.34/0.53    $false | (~spl4_6 | spl4_7)),
% 1.34/0.53    inference(subsumption_resolution,[],[f1194,f375])).
% 1.34/0.53  fof(f375,plain,(
% 1.34/0.53    ~r1_xboole_0(sK2,sK0) | spl4_7),
% 1.34/0.53    inference(avatar_component_clause,[],[f373])).
% 1.34/0.53  fof(f373,plain,(
% 1.34/0.53    spl4_7 <=> r1_xboole_0(sK2,sK0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.34/0.53  % (21473)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.34/0.53  fof(f1194,plain,(
% 1.34/0.53    r1_xboole_0(sK2,sK0) | ~spl4_6),
% 1.34/0.53    inference(resolution,[],[f614,f70])).
% 1.34/0.53  fof(f70,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.34/0.53    inference(superposition,[],[f34,f32])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f17])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.34/0.53    inference(rectify,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.34/0.53  fof(f614,plain,(
% 1.34/0.53    ( ! [X14] : (~r1_tarski(X14,sK2) | r1_xboole_0(X14,sK0)) ) | ~spl4_6),
% 1.34/0.53    inference(superposition,[],[f169,f239])).
% 1.34/0.53  fof(f239,plain,(
% 1.34/0.53    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl4_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f237])).
% 1.34/0.53  fof(f237,plain,(
% 1.34/0.53    spl4_6 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.34/0.53  fof(f169,plain,(
% 1.34/0.53    ( ! [X6,X4,X5,X3] : (r1_xboole_0(X6,k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5)))) | ~r1_tarski(X6,X5)) )),
% 1.34/0.53    inference(superposition,[],[f55,f54])).
% 1.34/0.53  fof(f54,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f44,f38,f38])).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.34/0.53  fof(f44,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.34/0.53  fof(f55,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f48,f38])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f14])).
% 1.34/0.53  fof(f14,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.34/0.53  fof(f1018,plain,(
% 1.34/0.53    spl4_5 | ~spl4_8),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f1017])).
% 1.34/0.53  fof(f1017,plain,(
% 1.34/0.53    $false | (spl4_5 | ~spl4_8)),
% 1.34/0.53    inference(subsumption_resolution,[],[f1016,f189])).
% 1.34/0.53  fof(f189,plain,(
% 1.34/0.53    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl4_5),
% 1.34/0.53    inference(avatar_component_clause,[],[f187])).
% 1.34/0.53  fof(f187,plain,(
% 1.34/0.53    spl4_5 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.34/0.53  fof(f1016,plain,(
% 1.34/0.53    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl4_8),
% 1.34/0.53    inference(forward_demodulation,[],[f1011,f347])).
% 1.34/0.53  fof(f347,plain,(
% 1.34/0.53    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.34/0.53    inference(superposition,[],[f84,f36])).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.34/0.53  fof(f84,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f34,f41])).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f9])).
% 1.34/0.53  fof(f9,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.34/0.53  fof(f1011,plain,(
% 1.34/0.53    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | ~spl4_8),
% 1.34/0.53    inference(resolution,[],[f753,f52])).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f43,f38])).
% 1.34/0.53  fof(f43,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.34/0.53    inference(nnf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.34/0.53  fof(f753,plain,(
% 1.34/0.53    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl4_8),
% 1.34/0.53    inference(avatar_component_clause,[],[f751])).
% 1.34/0.53  % (21477)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.34/0.53  fof(f751,plain,(
% 1.34/0.53    spl4_8 <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.34/0.53  fof(f754,plain,(
% 1.34/0.53    spl4_8 | ~spl4_6),
% 1.34/0.53    inference(avatar_split_clause,[],[f511,f237,f751])).
% 1.34/0.53  fof(f511,plain,(
% 1.34/0.53    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl4_6),
% 1.34/0.53    inference(superposition,[],[f171,f239])).
% 1.34/0.53  fof(f171,plain,(
% 1.34/0.53    ( ! [X12,X10,X11] : (r1_tarski(k3_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X11,X12))),k3_xboole_0(X10,X11))) )),
% 1.34/0.53    inference(superposition,[],[f50,f54])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f33,f38])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f10])).
% 1.34/0.53  fof(f10,axiom,(
% 1.34/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.34/0.53  fof(f376,plain,(
% 1.34/0.53    ~spl4_7 | ~spl4_4),
% 1.34/0.53    inference(avatar_split_clause,[],[f330,f182,f373])).
% 1.34/0.53  fof(f182,plain,(
% 1.34/0.53    spl4_4 <=> r2_hidden(sK3(sK0,sK2),k3_xboole_0(sK0,sK2))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.34/0.53  fof(f330,plain,(
% 1.34/0.53    ~r1_xboole_0(sK2,sK0) | ~spl4_4),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f184,f81])).
% 1.34/0.53  fof(f81,plain,(
% 1.34/0.53    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X3,X2)) | ~r1_xboole_0(X2,X3)) )),
% 1.34/0.53    inference(superposition,[],[f40,f36])).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.34/0.53    inference(ennf_transformation,[],[f18])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.34/0.53    inference(rectify,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.34/0.53  fof(f184,plain,(
% 1.34/0.53    r2_hidden(sK3(sK0,sK2),k3_xboole_0(sK0,sK2)) | ~spl4_4),
% 1.34/0.53    inference(avatar_component_clause,[],[f182])).
% 1.34/0.53  fof(f240,plain,(
% 1.34/0.53    spl4_6 | ~spl4_3),
% 1.34/0.53    inference(avatar_split_clause,[],[f86,f66,f237])).
% 1.34/0.53  fof(f66,plain,(
% 1.34/0.53    spl4_3 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.34/0.53  fof(f86,plain,(
% 1.34/0.53    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl4_3),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f68,f41])).
% 1.34/0.53  fof(f68,plain,(
% 1.34/0.53    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl4_3),
% 1.34/0.53    inference(avatar_component_clause,[],[f66])).
% 1.34/0.53  fof(f190,plain,(
% 1.34/0.53    ~spl4_5 | spl4_1),
% 1.34/0.53    inference(avatar_split_clause,[],[f127,f57,f187])).
% 1.34/0.53  fof(f57,plain,(
% 1.34/0.53    spl4_1 <=> r1_tarski(sK0,sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.34/0.53  fof(f127,plain,(
% 1.34/0.53    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl4_1),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f59,f53])).
% 1.34/0.53  fof(f53,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f42,f38])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f28])).
% 1.34/0.53  fof(f59,plain,(
% 1.34/0.53    ~r1_tarski(sK0,sK1) | spl4_1),
% 1.34/0.53    inference(avatar_component_clause,[],[f57])).
% 1.34/0.53  fof(f185,plain,(
% 1.34/0.53    spl4_4 | spl4_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f104,f61,f182])).
% 1.34/0.53  fof(f61,plain,(
% 1.34/0.53    spl4_2 <=> r1_xboole_0(sK0,sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.34/0.53  fof(f104,plain,(
% 1.34/0.53    r2_hidden(sK3(sK0,sK2),k3_xboole_0(sK0,sK2)) | spl4_2),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f63,f39])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f27])).
% 1.34/0.53  fof(f63,plain,(
% 1.34/0.53    ~r1_xboole_0(sK0,sK2) | spl4_2),
% 1.34/0.53    inference(avatar_component_clause,[],[f61])).
% 1.34/0.53  fof(f69,plain,(
% 1.34/0.53    spl4_3),
% 1.34/0.53    inference(avatar_split_clause,[],[f49,f66])).
% 1.34/0.53  fof(f49,plain,(
% 1.34/0.53    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.34/0.53    inference(definition_unfolding,[],[f29,f38])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.34/0.53    inference(cnf_transformation,[],[f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f24])).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.34/0.53    inference(ennf_transformation,[],[f16])).
% 1.34/0.53  fof(f16,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.34/0.53    inference(negated_conjecture,[],[f15])).
% 1.34/0.53  fof(f15,conjecture,(
% 1.34/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.34/0.53  fof(f64,plain,(
% 1.34/0.53    ~spl4_1 | ~spl4_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f30,f61,f57])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.34/0.53    inference(cnf_transformation,[],[f25])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (21486)------------------------------
% 1.34/0.53  % (21486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (21486)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (21486)Memory used [KB]: 11513
% 1.34/0.53  % (21486)Time elapsed: 0.098 s
% 1.34/0.53  % (21486)------------------------------
% 1.34/0.53  % (21486)------------------------------
% 1.34/0.53  % (21470)Success in time 0.175 s
%------------------------------------------------------------------------------
