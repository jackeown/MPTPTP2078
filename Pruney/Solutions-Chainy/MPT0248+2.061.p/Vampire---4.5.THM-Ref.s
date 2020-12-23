%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:58 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 612 expanded)
%              Number of leaves         :   29 ( 219 expanded)
%              Depth                    :   18
%              Number of atoms          :  335 (1020 expanded)
%              Number of equality atoms :  157 ( 719 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f122,f133,f153,f189,f195,f240,f245,f270,f275,f318,f340,f350,f412,f414,f576])).

fof(f576,plain,
    ( ~ spl6_20
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f575,f119,f359])).

fof(f359,plain,
    ( spl6_20
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f119,plain,
    ( spl6_4
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f575,plain,
    ( sK1 != sK2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f574,f120])).

fof(f120,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f574,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f573])).

fof(f573,plain,
    ( sK1 != sK1
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f69,f120])).

fof(f69,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f27,f67,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f21])).

% (14141)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f414,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f412,plain,
    ( ~ spl6_9
    | spl6_1
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f410,f347,f102,f192])).

% (14129)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f192,plain,
    ( spl6_9
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f102,plain,
    ( spl6_1
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f347,plain,
    ( spl6_19
  <=> sK0 = sK4(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f410,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl6_1
    | ~ spl6_19 ),
    inference(trivial_inequality_removal,[],[f409])).

fof(f409,plain,
    ( ~ r2_hidden(sK0,sK2)
    | sK2 != sK2
    | sK0 != sK0
    | spl6_1
    | ~ spl6_19 ),
    inference(superposition,[],[f110,f349])).

fof(f349,plain,
    ( sK0 = sK4(sK0,sK0,sK2)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f347])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,sK0,X0),X0)
        | sK2 != X0
        | sK0 != sK4(sK0,sK0,X0) )
    | spl6_1 ),
    inference(superposition,[],[f104,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | sK4(X0,X1,X2) != X0 ) ),
    inference(definition_unfolding,[],[f45,f65])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) != X0
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_tarski(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f104,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f350,plain,
    ( spl6_19
    | spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f174,f130,f102,f347])).

fof(f130,plain,
    ( spl6_5
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f174,plain,
    ( sK0 = sK4(sK0,sK0,sK2)
    | spl6_1
    | ~ spl6_5 ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( sK0 = sK4(sK0,sK0,sK2)
    | sK2 != sK2
    | spl6_1
    | ~ spl6_5 ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( sK0 = sK4(sK0,sK0,sK2)
    | sK0 = sK4(sK0,sK0,sK2)
    | sK2 != sK2
    | spl6_1
    | ~ spl6_5 ),
    inference(resolution,[],[f170,f113])).

fof(f113,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,X2),X2)
        | sK0 = sK4(sK0,sK0,X2)
        | sK2 != X2 )
    | spl6_1 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ! [X2] :
        ( sK2 != X2
        | sK0 = sK4(sK0,sK0,X2)
        | r2_hidden(sK4(sK0,sK0,X2),X2)
        | sK0 = sK4(sK0,sK0,X2) )
    | spl6_1 ),
    inference(superposition,[],[f104,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
      | sK4(X0,X1,X2) = X1
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sK4(X0,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) = X0
      | sK4(X0,X1,X2) = X1
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_tarski(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 = X0 )
    | ~ spl6_5 ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 = X0
        | sK0 = X0 )
    | ~ spl6_5 ),
    inference(resolution,[],[f146,f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f146,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl6_5 ),
    inference(superposition,[],[f98,f132])).

fof(f132,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f65])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
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

fof(f340,plain,
    ( spl6_2
    | spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl6_2
    | spl6_4
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f108,f121,f152,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f67,f67])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f152,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_6
  <=> r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f121,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f108,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f318,plain,
    ( spl6_16
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | spl6_16
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f269,f96,f302])).

fof(f302,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X5,k1_xboole_0) )
    | ~ spl6_17 ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X5,k1_xboole_0)
        | r2_hidden(X5,k1_xboole_0) )
    | ~ spl6_17 ),
    inference(superposition,[],[f100,f274])).

fof(f274,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl6_17
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f96,plain,(
    ! [X3,X1] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f49,f65])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f269,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl6_16
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f275,plain,
    ( spl6_17
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f251,f130,f115,f106,f272])).

fof(f115,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f251,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f199,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f199,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f132,f116])).

fof(f116,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f270,plain,
    ( ~ spl6_16
    | spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f265,f242,f237,f267])).

fof(f237,plain,
    ( spl6_14
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f242,plain,
    ( spl6_15
  <=> sK0 = sK4(sK0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f265,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl6_14
    | ~ spl6_15 ),
    inference(trivial_inequality_removal,[],[f264])).

fof(f264,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | sK0 != sK0
    | spl6_14
    | ~ spl6_15 ),
    inference(superposition,[],[f247,f244])).

fof(f244,plain,
    ( sK0 = sK4(sK0,sK0,k1_xboole_0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f242])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,sK0,X0),X0)
        | k1_xboole_0 != X0
        | sK0 != sK4(sK0,sK0,X0) )
    | spl6_14 ),
    inference(superposition,[],[f239,f84])).

fof(f239,plain,
    ( k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f237])).

fof(f245,plain,
    ( spl6_15
    | spl6_1
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f220,f130,f115,f102,f242])).

fof(f220,plain,
    ( sK0 = sK4(sK0,sK0,k1_xboole_0)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f174,f116])).

fof(f240,plain,
    ( ~ spl6_14
    | spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f196,f115,f102,f237])).

fof(f196,plain,
    ( k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl6_1
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f104,f116])).

fof(f195,plain,
    ( spl6_3
    | spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f190,f186,f192,f115])).

fof(f186,plain,
    ( spl6_8
  <=> sK0 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f190,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_8 ),
    inference(superposition,[],[f32,f188])).

fof(f188,plain,
    ( sK0 = sK3(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f186])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f189,plain,
    ( spl6_3
    | spl6_8
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f171,f130,f186,f115])).

fof(f171,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_5 ),
    inference(resolution,[],[f170,f32])).

fof(f153,plain,
    ( spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f141,f130,f150])).

fof(f141,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl6_5 ),
    inference(superposition,[],[f72,f132])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f66])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f133,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f68,f130])).

fof(f68,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f28,f67,f66])).

fof(f28,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f122,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f71,f119,f115])).

fof(f71,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f25,f67])).

fof(f25,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f70,f106,f102])).

fof(f70,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f26,f67])).

fof(f26,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:27:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (14149)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (14133)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (14126)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (14131)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (14128)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (14147)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (14121)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (14145)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (14143)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (14123)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (14135)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (14130)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (14137)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (14148)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (14124)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (14125)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (14139)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.48/0.56  % (14146)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.56  % (14149)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.56  % SZS output start Proof for theBenchmark
% 1.48/0.56  fof(f577,plain,(
% 1.48/0.56    $false),
% 1.48/0.56    inference(avatar_sat_refutation,[],[f109,f122,f133,f153,f189,f195,f240,f245,f270,f275,f318,f340,f350,f412,f414,f576])).
% 1.48/0.56  fof(f576,plain,(
% 1.48/0.56    ~spl6_20 | ~spl6_4),
% 1.48/0.56    inference(avatar_split_clause,[],[f575,f119,f359])).
% 1.48/0.56  fof(f359,plain,(
% 1.48/0.56    spl6_20 <=> sK1 = sK2),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.48/0.56  fof(f119,plain,(
% 1.48/0.56    spl6_4 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.48/0.56  fof(f575,plain,(
% 1.48/0.56    sK1 != sK2 | ~spl6_4),
% 1.48/0.56    inference(forward_demodulation,[],[f574,f120])).
% 1.48/0.56  fof(f120,plain,(
% 1.48/0.56    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl6_4),
% 1.48/0.56    inference(avatar_component_clause,[],[f119])).
% 1.48/0.56  fof(f574,plain,(
% 1.48/0.56    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl6_4),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f573])).
% 1.48/0.56  fof(f573,plain,(
% 1.48/0.56    sK1 != sK1 | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl6_4),
% 1.48/0.56    inference(forward_demodulation,[],[f69,f120])).
% 1.48/0.56  fof(f69,plain,(
% 1.48/0.56    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.48/0.56    inference(definition_unfolding,[],[f27,f67,f67])).
% 1.48/0.56  fof(f67,plain,(
% 1.48/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f31,f65])).
% 1.48/0.56  fof(f65,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f35,f64])).
% 1.48/0.56  fof(f64,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f44,f63])).
% 1.48/0.56  fof(f63,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f57,f62])).
% 1.48/0.56  fof(f62,plain,(
% 1.48/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f58,f61])).
% 1.48/0.56  fof(f61,plain,(
% 1.48/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f59,f60])).
% 1.48/0.56  fof(f60,plain,(
% 1.48/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f17])).
% 1.48/0.56  fof(f17,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.48/0.56  fof(f59,plain,(
% 1.48/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f16])).
% 1.48/0.56  fof(f16,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.48/0.56  fof(f58,plain,(
% 1.48/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f15])).
% 1.48/0.56  fof(f15,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.48/0.56  fof(f57,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f14])).
% 1.48/0.56  fof(f14,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.48/0.56  fof(f44,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f13])).
% 1.48/0.56  fof(f13,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.56  fof(f35,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f12])).
% 1.48/0.56  fof(f12,axiom,(
% 1.48/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.56  fof(f31,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f11])).
% 1.48/0.56  fof(f11,axiom,(
% 1.48/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.48/0.56  fof(f27,plain,(
% 1.48/0.56    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f22])).
% 1.48/0.56  fof(f22,plain,(
% 1.48/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.48/0.56    inference(ennf_transformation,[],[f21])).
% 1.48/0.56  % (14141)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.56  fof(f21,negated_conjecture,(
% 1.48/0.56    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.48/0.56    inference(negated_conjecture,[],[f20])).
% 1.48/0.56  fof(f20,conjecture,(
% 1.48/0.56    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.48/0.56  fof(f414,plain,(
% 1.48/0.56    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 = sK2),
% 1.48/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.48/0.56  fof(f412,plain,(
% 1.48/0.56    ~spl6_9 | spl6_1 | ~spl6_19),
% 1.48/0.56    inference(avatar_split_clause,[],[f410,f347,f102,f192])).
% 1.48/0.56  % (14129)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.48/0.56  fof(f192,plain,(
% 1.48/0.56    spl6_9 <=> r2_hidden(sK0,sK2)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.48/0.56  fof(f102,plain,(
% 1.48/0.56    spl6_1 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.48/0.56  fof(f347,plain,(
% 1.48/0.56    spl6_19 <=> sK0 = sK4(sK0,sK0,sK2)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.48/0.56  fof(f410,plain,(
% 1.48/0.56    ~r2_hidden(sK0,sK2) | (spl6_1 | ~spl6_19)),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f409])).
% 1.48/0.56  fof(f409,plain,(
% 1.48/0.56    ~r2_hidden(sK0,sK2) | sK2 != sK2 | sK0 != sK0 | (spl6_1 | ~spl6_19)),
% 1.48/0.56    inference(superposition,[],[f110,f349])).
% 1.48/0.56  fof(f349,plain,(
% 1.48/0.56    sK0 = sK4(sK0,sK0,sK2) | ~spl6_19),
% 1.48/0.56    inference(avatar_component_clause,[],[f347])).
% 1.48/0.56  fof(f110,plain,(
% 1.48/0.56    ( ! [X0] : (~r2_hidden(sK4(sK0,sK0,X0),X0) | sK2 != X0 | sK0 != sK4(sK0,sK0,X0)) ) | spl6_1),
% 1.48/0.56    inference(superposition,[],[f104,f84])).
% 1.48/0.56  fof(f84,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X2) | sK4(X0,X1,X2) != X0) )),
% 1.48/0.56    inference(definition_unfolding,[],[f45,f65])).
% 1.48/0.56  fof(f45,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (sK4(X0,X1,X2) != X0 | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_tarski(X0,X1) = X2) )),
% 1.48/0.56    inference(cnf_transformation,[],[f10])).
% 1.48/0.56  fof(f10,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.48/0.56  fof(f104,plain,(
% 1.48/0.56    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl6_1),
% 1.48/0.56    inference(avatar_component_clause,[],[f102])).
% 1.48/0.56  fof(f350,plain,(
% 1.48/0.56    spl6_19 | spl6_1 | ~spl6_5),
% 1.48/0.56    inference(avatar_split_clause,[],[f174,f130,f102,f347])).
% 1.48/0.56  fof(f130,plain,(
% 1.48/0.56    spl6_5 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.48/0.56  fof(f174,plain,(
% 1.48/0.56    sK0 = sK4(sK0,sK0,sK2) | (spl6_1 | ~spl6_5)),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f173])).
% 1.48/0.56  fof(f173,plain,(
% 1.48/0.56    sK0 = sK4(sK0,sK0,sK2) | sK2 != sK2 | (spl6_1 | ~spl6_5)),
% 1.48/0.56    inference(duplicate_literal_removal,[],[f172])).
% 1.48/0.56  fof(f172,plain,(
% 1.48/0.56    sK0 = sK4(sK0,sK0,sK2) | sK0 = sK4(sK0,sK0,sK2) | sK2 != sK2 | (spl6_1 | ~spl6_5)),
% 1.48/0.56    inference(resolution,[],[f170,f113])).
% 1.48/0.56  fof(f113,plain,(
% 1.48/0.56    ( ! [X2] : (r2_hidden(sK4(sK0,sK0,X2),X2) | sK0 = sK4(sK0,sK0,X2) | sK2 != X2) ) | spl6_1),
% 1.48/0.56    inference(duplicate_literal_removal,[],[f112])).
% 1.48/0.56  fof(f112,plain,(
% 1.48/0.56    ( ! [X2] : (sK2 != X2 | sK0 = sK4(sK0,sK0,X2) | r2_hidden(sK4(sK0,sK0,X2),X2) | sK0 = sK4(sK0,sK0,X2)) ) | spl6_1),
% 1.48/0.56    inference(superposition,[],[f104,f82])).
% 1.48/0.56  fof(f82,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 | sK4(X0,X1,X2) = X1 | r2_hidden(sK4(X0,X1,X2),X2) | sK4(X0,X1,X2) = X0) )),
% 1.48/0.56    inference(definition_unfolding,[],[f47,f65])).
% 1.48/0.56  fof(f47,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (sK4(X0,X1,X2) = X0 | sK4(X0,X1,X2) = X1 | r2_hidden(sK4(X0,X1,X2),X2) | k2_tarski(X0,X1) = X2) )),
% 1.48/0.56    inference(cnf_transformation,[],[f10])).
% 1.48/0.56  fof(f170,plain,(
% 1.48/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | sK0 = X0) ) | ~spl6_5),
% 1.48/0.56    inference(duplicate_literal_removal,[],[f164])).
% 1.48/0.56  fof(f164,plain,(
% 1.48/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | sK0 = X0 | sK0 = X0) ) | ~spl6_5),
% 1.48/0.56    inference(resolution,[],[f146,f97])).
% 1.48/0.56  fof(f97,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.48/0.56    inference(equality_resolution,[],[f81])).
% 1.48/0.56  fof(f81,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.48/0.56    inference(definition_unfolding,[],[f48,f65])).
% 1.48/0.56  fof(f48,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.48/0.56    inference(cnf_transformation,[],[f10])).
% 1.48/0.56  fof(f146,plain,(
% 1.48/0.56    ( ! [X3] : (r2_hidden(X3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X3,sK2)) ) | ~spl6_5),
% 1.48/0.56    inference(superposition,[],[f98,f132])).
% 1.48/0.56  fof(f132,plain,(
% 1.48/0.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl6_5),
% 1.48/0.56    inference(avatar_component_clause,[],[f130])).
% 1.48/0.56  fof(f98,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.48/0.56    inference(equality_resolution,[],[f85])).
% 1.48/0.56  fof(f85,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.48/0.56    inference(definition_unfolding,[],[f56,f66])).
% 1.48/0.56  fof(f66,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.48/0.56    inference(definition_unfolding,[],[f36,f65])).
% 1.48/0.56  fof(f36,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f19])).
% 1.48/0.56  fof(f19,axiom,(
% 1.48/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.48/0.56  fof(f56,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.48/0.56    inference(cnf_transformation,[],[f2])).
% 1.48/0.56  fof(f2,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.48/0.56  fof(f340,plain,(
% 1.48/0.56    spl6_2 | spl6_4 | ~spl6_6),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f334])).
% 1.48/0.56  fof(f334,plain,(
% 1.48/0.56    $false | (spl6_2 | spl6_4 | ~spl6_6)),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f108,f121,f152,f76])).
% 1.48/0.56  fof(f76,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.48/0.56    inference(definition_unfolding,[],[f39,f67,f67])).
% 1.48/0.56  fof(f39,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f18])).
% 1.48/0.56  fof(f18,axiom,(
% 1.48/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.48/0.56  fof(f152,plain,(
% 1.48/0.56    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl6_6),
% 1.48/0.56    inference(avatar_component_clause,[],[f150])).
% 1.48/0.56  fof(f150,plain,(
% 1.48/0.56    spl6_6 <=> r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.48/0.56  fof(f121,plain,(
% 1.48/0.56    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl6_4),
% 1.48/0.56    inference(avatar_component_clause,[],[f119])).
% 1.48/0.56  fof(f108,plain,(
% 1.48/0.56    k1_xboole_0 != sK1 | spl6_2),
% 1.48/0.56    inference(avatar_component_clause,[],[f106])).
% 1.48/0.56  fof(f106,plain,(
% 1.48/0.56    spl6_2 <=> k1_xboole_0 = sK1),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.48/0.56  fof(f318,plain,(
% 1.48/0.56    spl6_16 | ~spl6_17),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f307])).
% 1.48/0.56  fof(f307,plain,(
% 1.48/0.56    $false | (spl6_16 | ~spl6_17)),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f269,f96,f302])).
% 1.48/0.56  fof(f302,plain,(
% 1.48/0.56    ( ! [X5] : (~r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X5,k1_xboole_0)) ) | ~spl6_17),
% 1.48/0.56    inference(duplicate_literal_removal,[],[f301])).
% 1.48/0.56  fof(f301,plain,(
% 1.48/0.56    ( ! [X5] : (~r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X5,k1_xboole_0) | r2_hidden(X5,k1_xboole_0)) ) | ~spl6_17),
% 1.48/0.56    inference(superposition,[],[f100,f274])).
% 1.48/0.56  fof(f274,plain,(
% 1.48/0.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~spl6_17),
% 1.48/0.56    inference(avatar_component_clause,[],[f272])).
% 1.48/0.56  fof(f272,plain,(
% 1.48/0.56    spl6_17 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.48/0.56  fof(f100,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 1.48/0.56    inference(equality_resolution,[],[f87])).
% 1.48/0.56  fof(f87,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.48/0.56    inference(definition_unfolding,[],[f54,f66])).
% 1.48/0.56  fof(f54,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.48/0.56    inference(cnf_transformation,[],[f2])).
% 1.48/0.56  fof(f96,plain,(
% 1.48/0.56    ( ! [X3,X1] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))) )),
% 1.48/0.56    inference(equality_resolution,[],[f95])).
% 1.48/0.56  fof(f95,plain,(
% 1.48/0.56    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1) != X2) )),
% 1.48/0.56    inference(equality_resolution,[],[f80])).
% 1.48/0.56  fof(f80,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.48/0.56    inference(definition_unfolding,[],[f49,f65])).
% 1.48/0.56  fof(f49,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.48/0.56    inference(cnf_transformation,[],[f10])).
% 1.48/0.56  fof(f269,plain,(
% 1.48/0.56    ~r2_hidden(sK0,k1_xboole_0) | spl6_16),
% 1.48/0.56    inference(avatar_component_clause,[],[f267])).
% 1.48/0.56  fof(f267,plain,(
% 1.48/0.56    spl6_16 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.48/0.56  fof(f275,plain,(
% 1.48/0.56    spl6_17 | ~spl6_2 | ~spl6_3 | ~spl6_5),
% 1.48/0.56    inference(avatar_split_clause,[],[f251,f130,f115,f106,f272])).
% 1.48/0.56  fof(f115,plain,(
% 1.48/0.56    spl6_3 <=> k1_xboole_0 = sK2),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.48/0.56  fof(f251,plain,(
% 1.48/0.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.48/0.56    inference(forward_demodulation,[],[f199,f107])).
% 1.48/0.56  fof(f107,plain,(
% 1.48/0.56    k1_xboole_0 = sK1 | ~spl6_2),
% 1.48/0.56    inference(avatar_component_clause,[],[f106])).
% 1.48/0.56  fof(f199,plain,(
% 1.48/0.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) | (~spl6_3 | ~spl6_5)),
% 1.48/0.56    inference(backward_demodulation,[],[f132,f116])).
% 1.48/0.56  fof(f116,plain,(
% 1.48/0.56    k1_xboole_0 = sK2 | ~spl6_3),
% 1.48/0.56    inference(avatar_component_clause,[],[f115])).
% 1.48/0.56  fof(f270,plain,(
% 1.48/0.56    ~spl6_16 | spl6_14 | ~spl6_15),
% 1.48/0.56    inference(avatar_split_clause,[],[f265,f242,f237,f267])).
% 1.48/0.56  fof(f237,plain,(
% 1.48/0.56    spl6_14 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.48/0.56  fof(f242,plain,(
% 1.48/0.56    spl6_15 <=> sK0 = sK4(sK0,sK0,k1_xboole_0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.48/0.56  fof(f265,plain,(
% 1.48/0.56    ~r2_hidden(sK0,k1_xboole_0) | (spl6_14 | ~spl6_15)),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f264])).
% 1.48/0.56  fof(f264,plain,(
% 1.48/0.56    ~r2_hidden(sK0,k1_xboole_0) | k1_xboole_0 != k1_xboole_0 | sK0 != sK0 | (spl6_14 | ~spl6_15)),
% 1.48/0.56    inference(superposition,[],[f247,f244])).
% 1.48/0.57  fof(f244,plain,(
% 1.48/0.57    sK0 = sK4(sK0,sK0,k1_xboole_0) | ~spl6_15),
% 1.48/0.57    inference(avatar_component_clause,[],[f242])).
% 1.48/0.57  fof(f247,plain,(
% 1.48/0.57    ( ! [X0] : (~r2_hidden(sK4(sK0,sK0,X0),X0) | k1_xboole_0 != X0 | sK0 != sK4(sK0,sK0,X0)) ) | spl6_14),
% 1.48/0.57    inference(superposition,[],[f239,f84])).
% 1.48/0.57  fof(f239,plain,(
% 1.48/0.57    k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl6_14),
% 1.48/0.57    inference(avatar_component_clause,[],[f237])).
% 1.48/0.57  fof(f245,plain,(
% 1.48/0.57    spl6_15 | spl6_1 | ~spl6_3 | ~spl6_5),
% 1.48/0.57    inference(avatar_split_clause,[],[f220,f130,f115,f102,f242])).
% 1.48/0.57  fof(f220,plain,(
% 1.48/0.57    sK0 = sK4(sK0,sK0,k1_xboole_0) | (spl6_1 | ~spl6_3 | ~spl6_5)),
% 1.48/0.57    inference(forward_demodulation,[],[f174,f116])).
% 1.48/0.57  fof(f240,plain,(
% 1.48/0.57    ~spl6_14 | spl6_1 | ~spl6_3),
% 1.48/0.57    inference(avatar_split_clause,[],[f196,f115,f102,f237])).
% 1.48/0.57  fof(f196,plain,(
% 1.48/0.57    k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (spl6_1 | ~spl6_3)),
% 1.48/0.57    inference(backward_demodulation,[],[f104,f116])).
% 1.48/0.57  fof(f195,plain,(
% 1.48/0.57    spl6_3 | spl6_9 | ~spl6_8),
% 1.48/0.57    inference(avatar_split_clause,[],[f190,f186,f192,f115])).
% 1.48/0.57  fof(f186,plain,(
% 1.48/0.57    spl6_8 <=> sK0 = sK3(sK2)),
% 1.48/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.48/0.57  fof(f190,plain,(
% 1.48/0.57    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl6_8),
% 1.48/0.57    inference(superposition,[],[f32,f188])).
% 1.48/0.57  fof(f188,plain,(
% 1.48/0.57    sK0 = sK3(sK2) | ~spl6_8),
% 1.48/0.57    inference(avatar_component_clause,[],[f186])).
% 1.48/0.57  fof(f32,plain,(
% 1.48/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f23])).
% 1.48/0.57  fof(f23,plain,(
% 1.48/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.48/0.57    inference(ennf_transformation,[],[f3])).
% 1.48/0.57  fof(f3,axiom,(
% 1.48/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.48/0.57  fof(f189,plain,(
% 1.48/0.57    spl6_3 | spl6_8 | ~spl6_5),
% 1.48/0.57    inference(avatar_split_clause,[],[f171,f130,f186,f115])).
% 1.48/0.57  fof(f171,plain,(
% 1.48/0.57    sK0 = sK3(sK2) | k1_xboole_0 = sK2 | ~spl6_5),
% 1.48/0.57    inference(resolution,[],[f170,f32])).
% 1.48/0.57  fof(f153,plain,(
% 1.48/0.57    spl6_6 | ~spl6_5),
% 1.48/0.57    inference(avatar_split_clause,[],[f141,f130,f150])).
% 1.48/0.57  fof(f141,plain,(
% 1.48/0.57    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl6_5),
% 1.48/0.57    inference(superposition,[],[f72,f132])).
% 1.48/0.57  fof(f72,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f33,f66])).
% 1.48/0.57  fof(f33,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f9])).
% 1.48/0.57  fof(f9,axiom,(
% 1.48/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.48/0.57  fof(f133,plain,(
% 1.48/0.57    spl6_5),
% 1.48/0.57    inference(avatar_split_clause,[],[f68,f130])).
% 1.48/0.57  fof(f68,plain,(
% 1.48/0.57    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.48/0.57    inference(definition_unfolding,[],[f28,f67,f66])).
% 1.48/0.57  fof(f28,plain,(
% 1.48/0.57    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.48/0.57    inference(cnf_transformation,[],[f22])).
% 1.48/0.57  fof(f122,plain,(
% 1.48/0.57    ~spl6_3 | ~spl6_4),
% 1.48/0.57    inference(avatar_split_clause,[],[f71,f119,f115])).
% 1.48/0.57  fof(f71,plain,(
% 1.48/0.57    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.48/0.57    inference(definition_unfolding,[],[f25,f67])).
% 1.48/0.57  fof(f25,plain,(
% 1.48/0.57    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.48/0.57    inference(cnf_transformation,[],[f22])).
% 1.48/0.57  fof(f109,plain,(
% 1.48/0.57    ~spl6_1 | ~spl6_2),
% 1.48/0.57    inference(avatar_split_clause,[],[f70,f106,f102])).
% 1.48/0.57  fof(f70,plain,(
% 1.48/0.57    k1_xboole_0 != sK1 | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.48/0.57    inference(definition_unfolding,[],[f26,f67])).
% 1.48/0.57  fof(f26,plain,(
% 1.48/0.57    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.48/0.57    inference(cnf_transformation,[],[f22])).
% 1.48/0.57  % SZS output end Proof for theBenchmark
% 1.48/0.57  % (14149)------------------------------
% 1.48/0.57  % (14149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (14149)Termination reason: Refutation
% 1.48/0.57  
% 1.48/0.57  % (14149)Memory used [KB]: 11001
% 1.48/0.57  % (14149)Time elapsed: 0.138 s
% 1.48/0.57  % (14149)------------------------------
% 1.48/0.57  % (14149)------------------------------
% 1.48/0.57  % (14140)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.57  % (14132)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.48/0.57  % (14150)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.48/0.57  % (14150)Refutation not found, incomplete strategy% (14150)------------------------------
% 1.48/0.57  % (14150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (14150)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (14150)Memory used [KB]: 1663
% 1.48/0.57  % (14150)Time elapsed: 0.002 s
% 1.48/0.57  % (14150)------------------------------
% 1.48/0.57  % (14150)------------------------------
% 1.48/0.57  % (14142)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.48/0.57  % (14120)Success in time 0.203 s
%------------------------------------------------------------------------------
