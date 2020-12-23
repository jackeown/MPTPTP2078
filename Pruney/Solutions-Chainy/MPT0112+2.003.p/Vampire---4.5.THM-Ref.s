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
% DateTime   : Thu Dec  3 12:32:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 149 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  183 ( 307 expanded)
%              Number of equality atoms :   63 ( 117 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f57,f62,f79,f85,f109,f127,f141,f211,f236,f265,f266])).

fof(f266,plain,
    ( sK0 != sK1
    | r2_xboole_0(sK1,sK0)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f265,plain,
    ( spl2_20
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f264,f233,f69,f250])).

fof(f250,plain,
    ( spl2_20
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f69,plain,
    ( spl2_5
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f233,plain,
    ( spl2_18
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f264,plain,
    ( sK0 = sK1
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f247,f71])).

fof(f71,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f247,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_18 ),
    inference(superposition,[],[f23,f235])).

fof(f235,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f233])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f236,plain,
    ( spl2_18
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f223,f208,f138,f233])).

fof(f138,plain,
    ( spl2_11
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f208,plain,
    ( spl2_15
  <=> sK0 = k5_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f223,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f140,f210])).

fof(f210,plain,
    ( sK0 = k5_xboole_0(k1_xboole_0,sK0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f208])).

fof(f140,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f211,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f206,f121,f69,f40,f208])).

fof(f40,plain,
    ( spl2_1
  <=> k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f121,plain,
    ( spl2_10
  <=> k1_xboole_0 = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f206,plain,
    ( sK0 = k5_xboole_0(k1_xboole_0,sK0)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f198,f22])).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f198,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(superposition,[],[f152,f22])).

fof(f152,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(superposition,[],[f128,f102])).

fof(f102,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f81,f71])).

fof(f81,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl2_1 ),
    inference(superposition,[],[f33,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f128,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK1,X0))
    | ~ spl2_10 ),
    inference(superposition,[],[f33,f123])).

fof(f123,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f141,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f136,f69,f40,f138])).

fof(f136,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK0))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f133,f71])).

fof(f133,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f36,f102])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f127,plain,
    ( spl2_10
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f119,f106,f121])).

fof(f106,plain,
    ( spl2_8
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f119,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK1)
    | ~ spl2_8 ),
    inference(superposition,[],[f24,f108])).

fof(f108,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f109,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f103,f69,f40,f106])).

fof(f103,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f42,f71])).

fof(f85,plain,
    ( ~ spl2_6
    | spl2_4 ),
    inference(avatar_split_clause,[],[f83,f59,f74])).

fof(f74,plain,
    ( spl2_6
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f59,plain,
    ( spl2_4
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f83,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | spl2_4 ),
    inference(resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f61,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f79,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f67,f54,f69])).

fof(f54,plain,
    ( spl2_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f56,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f56,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f62,plain,
    ( ~ spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f49,f45,f59])).

fof(f45,plain,
    ( spl2_2
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f49,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f47,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f47,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f57,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f50,f45,f54])).

fof(f50,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f47,f29])).

fof(f48,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) )
   => ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X0)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f43,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f38,f40])).

fof(f38,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f35,f23])).

fof(f35,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f21,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (28304)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.49  % (28322)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.50  % (28322)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f267,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f43,f48,f57,f62,f79,f85,f109,f127,f141,f211,f236,f265,f266])).
% 0.20/0.51  fof(f266,plain,(
% 0.20/0.51    sK0 != sK1 | r2_xboole_0(sK1,sK0) | ~r2_xboole_0(sK0,sK1)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f265,plain,(
% 0.20/0.51    spl2_20 | ~spl2_5 | ~spl2_18),
% 0.20/0.51    inference(avatar_split_clause,[],[f264,f233,f69,f250])).
% 0.20/0.51  fof(f250,plain,(
% 0.20/0.51    spl2_20 <=> sK0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl2_5 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.51  fof(f233,plain,(
% 0.20/0.51    spl2_18 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.51  fof(f264,plain,(
% 0.20/0.51    sK0 = sK1 | (~spl2_5 | ~spl2_18)),
% 0.20/0.51    inference(forward_demodulation,[],[f247,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    sK0 = k3_xboole_0(sK0,sK1) | ~spl2_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f69])).
% 0.20/0.51  fof(f247,plain,(
% 0.20/0.51    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_18),
% 0.20/0.51    inference(superposition,[],[f23,f235])).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f233])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    spl2_18 | ~spl2_11 | ~spl2_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f223,f208,f138,f233])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    spl2_11 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    spl2_15 <=> sK0 = k5_xboole_0(k1_xboole_0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_11 | ~spl2_15)),
% 0.20/0.51    inference(backward_demodulation,[],[f140,f210])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    sK0 = k5_xboole_0(k1_xboole_0,sK0) | ~spl2_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f208])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    sK1 = k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK0)) | ~spl2_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f138])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    spl2_15 | ~spl2_1 | ~spl2_5 | ~spl2_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f206,f121,f69,f40,f208])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    spl2_1 <=> k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    spl2_10 <=> k1_xboole_0 = k5_xboole_0(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    sK0 = k5_xboole_0(k1_xboole_0,sK0) | (~spl2_1 | ~spl2_5 | ~spl2_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f198,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)) | (~spl2_1 | ~spl2_5 | ~spl2_10)),
% 0.20/0.51    inference(superposition,[],[f152,f22])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,X0))) ) | (~spl2_1 | ~spl2_5 | ~spl2_10)),
% 0.20/0.51    inference(superposition,[],[f128,f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_5)),
% 0.20/0.51    inference(backward_demodulation,[],[f81,f71])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0)) ) | ~spl2_1),
% 0.20/0.51    inference(superposition,[],[f33,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl2_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f40])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK1,X0))) ) | ~spl2_10),
% 0.20/0.51    inference(superposition,[],[f33,f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    k1_xboole_0 = k5_xboole_0(sK0,sK1) | ~spl2_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f121])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    spl2_11 | ~spl2_1 | ~spl2_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f136,f69,f40,f138])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    sK1 = k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK0)) | (~spl2_1 | ~spl2_5)),
% 0.20/0.51    inference(forward_demodulation,[],[f133,f71])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    sK1 = k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1))) | (~spl2_1 | ~spl2_5)),
% 0.20/0.51    inference(superposition,[],[f36,f102])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f25,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f26,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    spl2_10 | ~spl2_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f119,f106,f121])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    spl2_8 <=> k1_xboole_0 = k5_xboole_0(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    k1_xboole_0 = k5_xboole_0(sK0,sK1) | ~spl2_8),
% 0.20/0.51    inference(superposition,[],[f24,f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    k1_xboole_0 = k5_xboole_0(sK1,sK0) | ~spl2_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f106])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl2_8 | ~spl2_1 | ~spl2_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f103,f69,f40,f106])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    k1_xboole_0 = k5_xboole_0(sK1,sK0) | (~spl2_1 | ~spl2_5)),
% 0.20/0.51    inference(backward_demodulation,[],[f42,f71])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~spl2_6 | spl2_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f83,f59,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl2_6 <=> r2_xboole_0(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl2_4 <=> r1_tarski(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ~r2_xboole_0(sK1,sK0) | spl2_4),
% 0.20/0.51    inference(resolution,[],[f61,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~r1_tarski(sK1,sK0) | spl2_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl2_5 | ~spl2_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f67,f54,f69])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl2_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    sK0 = k3_xboole_0(sK0,sK1) | ~spl2_3),
% 0.20/0.51    inference(resolution,[],[f56,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | ~spl2_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ~spl2_4 | ~spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f49,f45,f59])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    spl2_2 <=> r2_xboole_0(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ~r1_tarski(sK1,sK0) | ~spl2_2),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f47,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    r2_xboole_0(sK0,sK1) | ~spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f45])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    spl2_3 | ~spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f45,f54])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | ~spl2_2),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f47,f29])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f20,f45])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    r2_xboole_0(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1)) => (k1_xboole_0 = k4_xboole_0(sK1,sK0) & r2_xboole_0(sK0,sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.20/0.51    inference(negated_conjecture,[],[f11])).
% 0.20/0.51  fof(f11,conjecture,(
% 0.20/0.51    ! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    spl2_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f40])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 0.20/0.51    inference(forward_demodulation,[],[f35,f23])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),
% 0.20/0.51    inference(definition_unfolding,[],[f21,f27])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (28322)------------------------------
% 0.20/0.51  % (28322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28322)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (28322)Memory used [KB]: 6396
% 0.20/0.51  % (28322)Time elapsed: 0.087 s
% 0.20/0.51  % (28322)------------------------------
% 0.20/0.51  % (28322)------------------------------
% 0.20/0.51  % (28289)Success in time 0.155 s
%------------------------------------------------------------------------------
