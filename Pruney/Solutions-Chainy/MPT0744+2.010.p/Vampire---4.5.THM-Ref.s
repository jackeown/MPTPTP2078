%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 151 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  262 ( 394 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f70,f125,f127,f194,f196,f204,f292,f320,f323,f331,f352])).

fof(f352,plain,
    ( spl4_2
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl4_2
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f27,f335,f103])).

fof(f103,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(factoring,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f335,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | spl4_2
    | ~ spl4_14 ),
    inference(superposition,[],[f68,f277])).

fof(f277,plain,
    ( sK0 = sK1
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl4_14
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f68,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_2
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f27,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f331,plain,
    ( spl4_9
    | spl4_14
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f328,f62,f275,f170])).

fof(f170,plain,
    ( spl4_9
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f62,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f328,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f63,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f28])).

fof(f28,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f63,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f323,plain,
    ( spl4_7
    | ~ spl4_3
    | ~ spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f322,f66,f120,f112,f136])).

fof(f136,plain,
    ( spl4_7
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f112,plain,
    ( spl4_3
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f120,plain,
    ( spl4_5
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f322,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | spl4_2 ),
    inference(resolution,[],[f68,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f320,plain,
    ( spl4_1
    | spl4_9
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl4_1
    | spl4_9
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f299,f57,f301,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f301,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl4_1
    | ~ spl4_14 ),
    inference(superposition,[],[f203,f277])).

fof(f203,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl4_1 ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f64,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f57,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f41,f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f299,plain,
    ( ~ r2_hidden(sK0,sK0)
    | spl4_9
    | ~ spl4_14 ),
    inference(superposition,[],[f171,f277])).

fof(f171,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f292,plain,
    ( ~ spl4_3
    | spl4_14
    | spl4_9
    | ~ spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f255,f116,f120,f170,f275,f112])).

fof(f116,plain,
    ( spl4_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f255,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f30,f198])).

fof(f198,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f118,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f118,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f204,plain,
    ( spl4_1
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl4_1
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f172,f64,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f172,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f196,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f195,f66,f120,f116,f112])).

fof(f195,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f67,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f67,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f194,plain,
    ( ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f146,f172])).

fof(f146,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f138,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f138,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f127,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f26,f122])).

fof(f122,plain,
    ( ~ v3_ordinal1(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f26,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f125,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f27,f114])).

fof(f114,plain,
    ( ~ v3_ordinal1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f70,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f50,f66,f62])).

fof(f50,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f24,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f49,f66,f62])).

fof(f49,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f25,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:21:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (26893)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (26886)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (26883)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (26882)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (26893)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f353,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f69,f70,f125,f127,f194,f196,f204,f292,f320,f323,f331,f352])).
% 0.21/0.55  fof(f352,plain,(
% 0.21/0.55    spl4_2 | ~spl4_14),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f344])).
% 0.21/0.55  fof(f344,plain,(
% 0.21/0.55    $false | (spl4_2 | ~spl4_14)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f27,f335,f103])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(factoring,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.55  fof(f335,plain,(
% 0.21/0.55    ~r1_ordinal1(sK0,sK0) | (spl4_2 | ~spl4_14)),
% 0.21/0.55    inference(superposition,[],[f68,f277])).
% 0.21/0.55  fof(f277,plain,(
% 0.21/0.55    sK0 = sK1 | ~spl4_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f275])).
% 0.21/0.55  fof(f275,plain,(
% 0.21/0.55    spl4_14 <=> sK0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ~r1_ordinal1(sK0,sK1) | spl4_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    spl4_2 <=> r1_ordinal1(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    v3_ordinal1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.55    inference(negated_conjecture,[],[f11])).
% 0.21/0.55  fof(f11,conjecture,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.21/0.55  fof(f331,plain,(
% 0.21/0.55    spl4_9 | spl4_14 | ~spl4_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f328,f62,f275,f170])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    spl4_9 <=> r2_hidden(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    spl4_1 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.55  fof(f328,plain,(
% 0.21/0.55    sK0 = sK1 | r2_hidden(sK0,sK1) | ~spl4_1),
% 0.21/0.55    inference(resolution,[],[f63,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 = X1 | r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f39,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl4_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f62])).
% 0.21/0.55  fof(f323,plain,(
% 0.21/0.55    spl4_7 | ~spl4_3 | ~spl4_5 | spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f322,f66,f120,f112,f136])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    spl4_7 <=> r2_hidden(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    spl4_3 <=> v3_ordinal1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    spl4_5 <=> v3_ordinal1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.55  fof(f322,plain,(
% 0.21/0.55    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | spl4_2),
% 0.21/0.55    inference(resolution,[],[f68,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.55  fof(f320,plain,(
% 0.21/0.55    spl4_1 | spl4_9 | ~spl4_14),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f315])).
% 0.21/0.55  fof(f315,plain,(
% 0.21/0.55    $false | (spl4_1 | spl4_9 | ~spl4_14)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f299,f57,f301,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.56  fof(f301,plain,(
% 0.21/0.56    ~r2_hidden(sK0,k1_tarski(sK0)) | (spl4_1 | ~spl4_14)),
% 0.21/0.56    inference(superposition,[],[f203,f277])).
% 0.21/0.56  fof(f203,plain,(
% 0.21/0.56    ~r2_hidden(sK0,k1_tarski(sK1)) | spl4_1),
% 0.21/0.56    inference(resolution,[],[f64,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | spl4_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f62])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 0.21/0.56    inference(equality_resolution,[],[f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0,X1] : (X0 != X1 | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f41,f28])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (X0 != X1 | r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f299,plain,(
% 0.21/0.56    ~r2_hidden(sK0,sK0) | (spl4_9 | ~spl4_14)),
% 0.21/0.56    inference(superposition,[],[f171,f277])).
% 0.21/0.56  fof(f171,plain,(
% 0.21/0.56    ~r2_hidden(sK0,sK1) | spl4_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f170])).
% 0.21/0.56  fof(f292,plain,(
% 0.21/0.56    ~spl4_3 | spl4_14 | spl4_9 | ~spl4_5 | ~spl4_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f255,f116,f120,f170,f275,f112])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    spl4_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.56  fof(f255,plain,(
% 0.21/0.56    ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~spl4_4),
% 0.21/0.56    inference(resolution,[],[f30,f198])).
% 0.21/0.56  fof(f198,plain,(
% 0.21/0.56    ~r2_hidden(sK1,sK0) | ~spl4_4),
% 0.21/0.56    inference(resolution,[],[f118,f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    r1_tarski(sK0,sK1) | ~spl4_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f116])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.56    inference(flattening,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    spl4_1 | ~spl4_9),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f201])).
% 0.21/0.56  fof(f201,plain,(
% 0.21/0.56    $false | (spl4_1 | ~spl4_9)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f172,f64,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    r2_hidden(sK0,sK1) | ~spl4_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f170])).
% 0.21/0.56  fof(f196,plain,(
% 0.21/0.56    ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f195,f66,f120,f116,f112])).
% 0.21/0.56  fof(f195,plain,(
% 0.21/0.56    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl4_2),
% 0.21/0.56    inference(resolution,[],[f67,f34])).
% 1.36/0.56  fof(f34,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f22])).
% 1.36/0.56  fof(f22,plain,(
% 1.36/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.36/0.56    inference(flattening,[],[f21])).
% 1.36/0.56  fof(f21,plain,(
% 1.36/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f6])).
% 1.36/0.56  fof(f6,axiom,(
% 1.36/0.56    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.36/0.56  fof(f67,plain,(
% 1.36/0.56    r1_ordinal1(sK0,sK1) | ~spl4_2),
% 1.36/0.56    inference(avatar_component_clause,[],[f66])).
% 1.36/0.56  fof(f194,plain,(
% 1.36/0.56    ~spl4_7 | ~spl4_9),
% 1.36/0.56    inference(avatar_contradiction_clause,[],[f186])).
% 1.36/0.56  fof(f186,plain,(
% 1.36/0.56    $false | (~spl4_7 | ~spl4_9)),
% 1.36/0.56    inference(subsumption_resolution,[],[f146,f172])).
% 1.36/0.56  fof(f146,plain,(
% 1.36/0.56    ~r2_hidden(sK0,sK1) | ~spl4_7),
% 1.36/0.56    inference(resolution,[],[f138,f31])).
% 1.36/0.56  fof(f31,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f18])).
% 1.36/0.56  fof(f18,plain,(
% 1.36/0.56    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.36/0.56    inference(ennf_transformation,[],[f1])).
% 1.36/0.56  fof(f1,axiom,(
% 1.36/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.36/0.56  fof(f138,plain,(
% 1.36/0.56    r2_hidden(sK1,sK0) | ~spl4_7),
% 1.36/0.56    inference(avatar_component_clause,[],[f136])).
% 1.36/0.56  fof(f127,plain,(
% 1.36/0.56    spl4_5),
% 1.36/0.56    inference(avatar_contradiction_clause,[],[f126])).
% 1.36/0.56  fof(f126,plain,(
% 1.36/0.56    $false | spl4_5),
% 1.36/0.56    inference(subsumption_resolution,[],[f26,f122])).
% 1.36/0.56  fof(f122,plain,(
% 1.36/0.56    ~v3_ordinal1(sK1) | spl4_5),
% 1.36/0.56    inference(avatar_component_clause,[],[f120])).
% 1.36/0.56  fof(f26,plain,(
% 1.36/0.56    v3_ordinal1(sK1)),
% 1.36/0.56    inference(cnf_transformation,[],[f13])).
% 1.36/0.56  fof(f125,plain,(
% 1.36/0.56    spl4_3),
% 1.36/0.56    inference(avatar_contradiction_clause,[],[f124])).
% 1.36/0.56  fof(f124,plain,(
% 1.36/0.56    $false | spl4_3),
% 1.36/0.56    inference(subsumption_resolution,[],[f27,f114])).
% 1.36/0.56  fof(f114,plain,(
% 1.36/0.56    ~v3_ordinal1(sK0) | spl4_3),
% 1.36/0.56    inference(avatar_component_clause,[],[f112])).
% 1.36/0.56  fof(f70,plain,(
% 1.36/0.56    spl4_1 | spl4_2),
% 1.36/0.56    inference(avatar_split_clause,[],[f50,f66,f62])).
% 1.36/0.56  fof(f50,plain,(
% 1.36/0.56    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.36/0.56    inference(definition_unfolding,[],[f24,f28])).
% 1.36/0.56  fof(f24,plain,(
% 1.36/0.56    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.36/0.56    inference(cnf_transformation,[],[f13])).
% 1.36/0.56  fof(f69,plain,(
% 1.36/0.56    ~spl4_1 | ~spl4_2),
% 1.36/0.56    inference(avatar_split_clause,[],[f49,f66,f62])).
% 1.36/0.56  fof(f49,plain,(
% 1.36/0.56    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.36/0.56    inference(definition_unfolding,[],[f25,f28])).
% 1.36/0.56  fof(f25,plain,(
% 1.36/0.56    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.36/0.56    inference(cnf_transformation,[],[f13])).
% 1.36/0.56  % SZS output end Proof for theBenchmark
% 1.36/0.56  % (26893)------------------------------
% 1.36/0.56  % (26893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (26893)Termination reason: Refutation
% 1.36/0.56  
% 1.36/0.56  % (26893)Memory used [KB]: 6396
% 1.36/0.56  % (26893)Time elapsed: 0.025 s
% 1.36/0.56  % (26893)------------------------------
% 1.36/0.56  % (26893)------------------------------
% 1.36/0.56  % (26874)Success in time 0.196 s
%------------------------------------------------------------------------------
