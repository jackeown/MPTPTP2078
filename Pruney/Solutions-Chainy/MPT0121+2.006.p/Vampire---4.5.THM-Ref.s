%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 150 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  160 ( 343 expanded)
%              Number of equality atoms :   27 (  61 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f56,f63,f71,f76,f120,f127,f181,f186,f254,f260])).

fof(f260,plain,
    ( ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16 ),
    inference(subsumption_resolution,[],[f258,f185])).

fof(f185,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_15
  <=> sK3 = k4_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f258,plain,
    ( sK3 != k4_xboole_0(sK3,sK2)
    | ~ spl4_12
    | ~ spl4_14
    | spl4_16 ),
    inference(forward_demodulation,[],[f257,f180])).

fof(f180,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl4_14
  <=> sK3 = k4_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f257,plain,
    ( sK3 != k4_xboole_0(k4_xboole_0(sK3,sK1),sK2)
    | ~ spl4_12
    | spl4_16 ),
    inference(forward_demodulation,[],[f256,f126])).

fof(f126,plain,
    ( sK3 = k4_xboole_0(sK3,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_12
  <=> sK3 = k4_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f256,plain,
    ( sK3 != k4_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK0),sK1),sK2)
    | spl4_16 ),
    inference(superposition,[],[f253,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0) ),
    inference(forward_demodulation,[],[f64,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f21,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[],[f23,f23])).

fof(f253,plain,
    ( sK3 != k4_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl4_16
  <=> sK3 = k4_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f254,plain,
    ( ~ spl4_16
    | spl4_11 ),
    inference(avatar_split_clause,[],[f121,f117,f251])).

fof(f117,plain,
    ( spl4_11
  <=> r1_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f121,plain,
    ( sK3 != k4_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)))
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f119,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f119,plain,
    ( ~ r1_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f186,plain,
    ( spl4_15
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f85,f73,f183])).

fof(f73,plain,
    ( spl4_7
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f85,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f75,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f181,plain,
    ( spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f81,f68,f178])).

fof(f68,plain,
    ( spl4_6
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f81,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f70,f19])).

fof(f70,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f127,plain,
    ( spl4_12
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f77,f60,f124])).

fof(f60,plain,
    ( spl4_5
  <=> r1_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f77,plain,
    ( sK3 = k4_xboole_0(sK3,sK0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f62,f19])).

fof(f62,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f120,plain,
    ( ~ spl4_11
    | spl4_4 ),
    inference(avatar_split_clause,[],[f58,f53,f117])).

fof(f53,plain,
    ( spl4_4
  <=> r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f58,plain,
    ( ~ r1_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)))
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f55,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f55,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)),sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f76,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f42,f36,f73])).

fof(f36,plain,
    ( spl4_3
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f42,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f38,f18])).

fof(f38,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f71,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f41,f31,f68])).

fof(f31,plain,
    ( spl4_2
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f41,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f33,f18])).

fof(f33,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f63,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f40,f26,f60])).

fof(f26,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f40,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f28,f18])).

fof(f28,plain,
    ( r1_xboole_0(sK0,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f56,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ~ r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)),sK3) ),
    inference(backward_demodulation,[],[f22,f23])).

fof(f22,plain,(
    ~ r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),sK3) ),
    inference(definition_unfolding,[],[f16,f17,f17])).

fof(f16,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
        & r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
   => ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f15,f36])).

fof(f15,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f13,f26])).

fof(f13,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:59:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (21504)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.44  % (21504)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f261,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f29,f34,f39,f56,f63,f71,f76,f120,f127,f181,f186,f254,f260])).
% 0.22/0.44  fof(f260,plain,(
% 0.22/0.44    ~spl4_12 | ~spl4_14 | ~spl4_15 | spl4_16),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f259])).
% 0.22/0.44  fof(f259,plain,(
% 0.22/0.44    $false | (~spl4_12 | ~spl4_14 | ~spl4_15 | spl4_16)),
% 0.22/0.44    inference(subsumption_resolution,[],[f258,f185])).
% 0.22/0.44  fof(f185,plain,(
% 0.22/0.44    sK3 = k4_xboole_0(sK3,sK2) | ~spl4_15),
% 0.22/0.44    inference(avatar_component_clause,[],[f183])).
% 0.22/0.44  fof(f183,plain,(
% 0.22/0.44    spl4_15 <=> sK3 = k4_xboole_0(sK3,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.44  fof(f258,plain,(
% 0.22/0.44    sK3 != k4_xboole_0(sK3,sK2) | (~spl4_12 | ~spl4_14 | spl4_16)),
% 0.22/0.44    inference(forward_demodulation,[],[f257,f180])).
% 0.22/0.44  fof(f180,plain,(
% 0.22/0.44    sK3 = k4_xboole_0(sK3,sK1) | ~spl4_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f178])).
% 0.22/0.44  fof(f178,plain,(
% 0.22/0.44    spl4_14 <=> sK3 = k4_xboole_0(sK3,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.44  fof(f257,plain,(
% 0.22/0.44    sK3 != k4_xboole_0(k4_xboole_0(sK3,sK1),sK2) | (~spl4_12 | spl4_16)),
% 0.22/0.44    inference(forward_demodulation,[],[f256,f126])).
% 0.22/0.44  fof(f126,plain,(
% 0.22/0.44    sK3 = k4_xboole_0(sK3,sK0) | ~spl4_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f124])).
% 0.22/0.44  fof(f124,plain,(
% 0.22/0.44    spl4_12 <=> sK3 = k4_xboole_0(sK3,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.44  fof(f256,plain,(
% 0.22/0.44    sK3 != k4_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK0),sK1),sK2) | spl4_16),
% 0.22/0.44    inference(superposition,[],[f253,f66])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f64,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f21,f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 0.22/0.44    inference(superposition,[],[f23,f23])).
% 0.22/0.44  fof(f253,plain,(
% 0.22/0.44    sK3 != k4_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1))) | spl4_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f251])).
% 0.22/0.44  fof(f251,plain,(
% 0.22/0.44    spl4_16 <=> sK3 = k4_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.44  fof(f254,plain,(
% 0.22/0.44    ~spl4_16 | spl4_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f121,f117,f251])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    spl4_11 <=> r1_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.44  fof(f121,plain,(
% 0.22/0.44    sK3 != k4_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1))) | spl4_11),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f119,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(nnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.44  fof(f119,plain,(
% 0.22/0.44    ~r1_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1))) | spl4_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f117])).
% 0.22/0.44  fof(f186,plain,(
% 0.22/0.44    spl4_15 | ~spl4_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f85,f73,f183])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    spl4_7 <=> r1_xboole_0(sK3,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    sK3 = k4_xboole_0(sK3,sK2) | ~spl4_7),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f75,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    r1_xboole_0(sK3,sK2) | ~spl4_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f73])).
% 0.22/0.44  fof(f181,plain,(
% 0.22/0.44    spl4_14 | ~spl4_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f81,f68,f178])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl4_6 <=> r1_xboole_0(sK3,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    sK3 = k4_xboole_0(sK3,sK1) | ~spl4_6),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f70,f19])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    r1_xboole_0(sK3,sK1) | ~spl4_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f68])).
% 0.22/0.44  fof(f127,plain,(
% 0.22/0.44    spl4_12 | ~spl4_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f77,f60,f124])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    spl4_5 <=> r1_xboole_0(sK3,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    sK3 = k4_xboole_0(sK3,sK0) | ~spl4_5),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f62,f19])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    r1_xboole_0(sK3,sK0) | ~spl4_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f60])).
% 0.22/0.44  fof(f120,plain,(
% 0.22/0.44    ~spl4_11 | spl4_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f58,f53,f117])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl4_4 <=> r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)),sK3)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ~r1_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1))) | spl4_4),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f55,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    ~r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)),sK3) | spl4_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    spl4_7 | ~spl4_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f42,f36,f73])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    spl4_3 <=> r1_xboole_0(sK2,sK3)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    r1_xboole_0(sK3,sK2) | ~spl4_3),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f38,f18])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    r1_xboole_0(sK2,sK3) | ~spl4_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f36])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    spl4_6 | ~spl4_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f41,f31,f68])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    spl4_2 <=> r1_xboole_0(sK1,sK3)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    r1_xboole_0(sK3,sK1) | ~spl4_2),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f33,f18])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    r1_xboole_0(sK1,sK3) | ~spl4_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f31])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl4_5 | ~spl4_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f40,f26,f60])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    spl4_1 <=> r1_xboole_0(sK0,sK3)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    r1_xboole_0(sK3,sK0) | ~spl4_1),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f28,f18])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    r1_xboole_0(sK0,sK3) | ~spl4_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f26])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ~spl4_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f53])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ~r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK2,sK0),sK1)),sK3)),
% 0.22/0.44    inference(backward_demodulation,[],[f22,f23])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ~r1_xboole_0(k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),sK3)),
% 0.22/0.44    inference(definition_unfolding,[],[f16,f17,f17])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 0.22/0.44    inference(flattening,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.22/0.44    inference(negated_conjecture,[],[f5])).
% 0.22/0.44  fof(f5,conjecture,(
% 0.22/0.44    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    spl4_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f15,f36])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    r1_xboole_0(sK2,sK3)),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    spl4_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f14,f31])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    r1_xboole_0(sK1,sK3)),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    spl4_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f13,f26])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    r1_xboole_0(sK0,sK3)),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (21504)------------------------------
% 0.22/0.44  % (21504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (21504)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (21504)Memory used [KB]: 10874
% 0.22/0.44  % (21504)Time elapsed: 0.017 s
% 0.22/0.44  % (21504)------------------------------
% 0.22/0.44  % (21504)------------------------------
% 0.22/0.45  % (21488)Success in time 0.082 s
%------------------------------------------------------------------------------
