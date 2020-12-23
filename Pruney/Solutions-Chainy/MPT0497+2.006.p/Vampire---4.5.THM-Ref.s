%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 191 expanded)
%              Number of leaves         :   26 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  251 ( 450 expanded)
%              Number of equality atoms :   73 ( 150 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f80,f87,f139,f146,f148,f166,f206,f330,f929,f1020,f1230,f1234])).

fof(f1234,plain,(
    ~ spl3_58 ),
    inference(avatar_contradiction_clause,[],[f1231])).

fof(f1231,plain,
    ( $false
    | ~ spl3_58 ),
    inference(unit_resulting_resolution,[],[f320,f1229])).

fof(f1229,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0)
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f1227])).

fof(f1227,plain,
    ( spl3_58
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f320,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f314,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f314,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f97,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f97,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f35,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1230,plain,
    ( spl3_58
    | spl3_11
    | ~ spl3_18
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f1177,f927,f203,f136,f1227])).

fof(f136,plain,
    ( spl3_11
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f203,plain,
    ( spl3_18
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f927,plain,
    ( spl3_55
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f1177,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0)
    | spl3_11
    | ~ spl3_18
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f1176,f204])).

fof(f204,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f203])).

fof(f1176,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,sK0)))
    | spl3_11
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f1175,f946])).

fof(f946,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(sK1)))
    | ~ spl3_55 ),
    inference(superposition,[],[f50,f928])).

fof(f928,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f927])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f39,f40,f40])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

% (7982)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f1175,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
    | spl3_11 ),
    inference(forward_demodulation,[],[f1172,f50])).

fof(f1172,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)))
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f137,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f137,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f1020,plain,
    ( ~ spl3_12
    | spl3_18
    | ~ spl3_55 ),
    inference(avatar_contradiction_clause,[],[f1019])).

fof(f1019,plain,
    ( $false
    | ~ spl3_12
    | spl3_18
    | ~ spl3_55 ),
    inference(global_subsumption,[],[f205,f960])).

fof(f960,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_12
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f930,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f49,f35])).

fof(f930,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl3_12
    | ~ spl3_55 ),
    inference(superposition,[],[f928,f145])).

fof(f145,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_12
  <=> k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f205,plain,
    ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f203])).

fof(f929,plain,
    ( spl3_55
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f846,f56,f927])).

fof(f56,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f846,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f46,f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f58,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f330,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,k1_xboole_0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0)
    | k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f206,plain,
    ( ~ spl3_18
    | ~ spl3_2
    | spl3_10 ),
    inference(avatar_split_clause,[],[f155,f132,f62,f203])).

fof(f62,plain,
    ( spl3_2
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f132,plain,
    ( spl3_10
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f155,plain,
    ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_2
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f63,f133,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f133,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f63,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f166,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f156,f84,f62,f163])).

fof(f163,plain,
    ( spl3_14
  <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f84,plain,
    ( spl3_5
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f156,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f63,f86,f36])).

fof(f86,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f148,plain,
    ( ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f33,f136,f132])).

fof(f33,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f146,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f140,f136,f143])).

fof(f140,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f138,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f138,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f32,f136,f132])).

fof(f32,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f81,f78,f84])).

fof(f78,plain,
    ( spl3_4
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f81,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f79,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f79,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f73,f56,f78])).

fof(f73,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f64,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f60,f56,f62])).

fof(f60,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f58,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f59,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:25:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.41  % (7994)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.44  % (7994)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f1235,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(avatar_sat_refutation,[],[f59,f64,f80,f87,f139,f146,f148,f166,f206,f330,f929,f1020,f1230,f1234])).
% 0.19/0.44  fof(f1234,plain,(
% 0.19/0.44    ~spl3_58),
% 0.19/0.44    inference(avatar_contradiction_clause,[],[f1231])).
% 0.19/0.44  fof(f1231,plain,(
% 0.19/0.44    $false | ~spl3_58),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f320,f1229])).
% 0.19/0.44  fof(f1229,plain,(
% 0.19/0.44    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0) | ~spl3_58),
% 0.19/0.44    inference(avatar_component_clause,[],[f1227])).
% 0.19/0.44  fof(f1227,plain,(
% 0.19/0.44    spl3_58 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.19/0.44  fof(f320,plain,(
% 0.19/0.44    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.44    inference(forward_demodulation,[],[f314,f49])).
% 0.19/0.44  fof(f49,plain,(
% 0.19/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.19/0.44    inference(definition_unfolding,[],[f34,f40])).
% 0.19/0.44  fof(f40,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f7])).
% 0.19/0.44  fof(f7,axiom,(
% 0.19/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.44  fof(f34,plain,(
% 0.19/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.44  fof(f314,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) )),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f97,f52])).
% 0.19/0.44  fof(f52,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.19/0.44    inference(definition_unfolding,[],[f43,f40])).
% 0.19/0.44  fof(f43,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f29])).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f28])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f20,plain,(
% 0.19/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.44    inference(ennf_transformation,[],[f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.44    inference(rectify,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.19/0.44  fof(f97,plain,(
% 0.19/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f35,f48])).
% 0.19/0.44  fof(f48,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.19/0.44    inference(cnf_transformation,[],[f30])).
% 0.19/0.44  fof(f30,plain,(
% 0.19/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.44    inference(nnf_transformation,[],[f8])).
% 0.19/0.44  fof(f8,axiom,(
% 0.19/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.44  fof(f35,plain,(
% 0.19/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.44    inference(cnf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.44  fof(f1230,plain,(
% 0.19/0.44    spl3_58 | spl3_11 | ~spl3_18 | ~spl3_55),
% 0.19/0.44    inference(avatar_split_clause,[],[f1177,f927,f203,f136,f1227])).
% 0.19/0.44  fof(f136,plain,(
% 0.19/0.44    spl3_11 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.44  fof(f203,plain,(
% 0.19/0.44    spl3_18 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.19/0.44  fof(f927,plain,(
% 0.19/0.44    spl3_55 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.19/0.44  fof(f1177,plain,(
% 0.19/0.44    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0) | (spl3_11 | ~spl3_18 | ~spl3_55)),
% 0.19/0.44    inference(forward_demodulation,[],[f1176,f204])).
% 0.19/0.44  fof(f204,plain,(
% 0.19/0.44    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl3_18),
% 0.19/0.44    inference(avatar_component_clause,[],[f203])).
% 0.19/0.44  fof(f1176,plain,(
% 0.19/0.44    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,sK0))) | (spl3_11 | ~spl3_55)),
% 0.19/0.44    inference(forward_demodulation,[],[f1175,f946])).
% 0.19/0.44  fof(f946,plain,(
% 0.19/0.44    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(sK1)))) ) | ~spl3_55),
% 0.19/0.44    inference(superposition,[],[f50,f928])).
% 0.19/0.44  fof(f928,plain,(
% 0.19/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))) ) | ~spl3_55),
% 0.19/0.44    inference(avatar_component_clause,[],[f927])).
% 0.19/0.44  fof(f50,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.19/0.44    inference(definition_unfolding,[],[f39,f40,f40])).
% 0.19/0.44  fof(f39,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.44  % (7982)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.44  fof(f1175,plain,(
% 0.19/0.44    r2_hidden(sK2(k1_relat_1(sK1),sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) | spl3_11),
% 0.19/0.44    inference(forward_demodulation,[],[f1172,f50])).
% 0.19/0.44  fof(f1172,plain,(
% 0.19/0.44    r2_hidden(sK2(k1_relat_1(sK1),sK0),k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) | spl3_11),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f137,f53])).
% 0.19/0.44  fof(f53,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.19/0.44    inference(definition_unfolding,[],[f42,f40])).
% 0.19/0.44  fof(f42,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f29])).
% 0.19/0.44  fof(f137,plain,(
% 0.19/0.44    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl3_11),
% 0.19/0.44    inference(avatar_component_clause,[],[f136])).
% 0.19/0.44  fof(f1020,plain,(
% 0.19/0.44    ~spl3_12 | spl3_18 | ~spl3_55),
% 0.19/0.44    inference(avatar_contradiction_clause,[],[f1019])).
% 0.19/0.44  fof(f1019,plain,(
% 0.19/0.44    $false | (~spl3_12 | spl3_18 | ~spl3_55)),
% 0.19/0.44    inference(global_subsumption,[],[f205,f960])).
% 0.19/0.44  fof(f960,plain,(
% 0.19/0.44    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl3_12 | ~spl3_55)),
% 0.19/0.44    inference(forward_demodulation,[],[f930,f71])).
% 0.19/0.44  fof(f71,plain,(
% 0.19/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.19/0.44    inference(superposition,[],[f49,f35])).
% 0.19/0.44  fof(f930,plain,(
% 0.19/0.44    k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) | (~spl3_12 | ~spl3_55)),
% 0.19/0.44    inference(superposition,[],[f928,f145])).
% 0.19/0.44  fof(f145,plain,(
% 0.19/0.44    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) | ~spl3_12),
% 0.19/0.44    inference(avatar_component_clause,[],[f143])).
% 0.19/0.44  fof(f143,plain,(
% 0.19/0.44    spl3_12 <=> k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.44  fof(f205,plain,(
% 0.19/0.44    k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0)) | spl3_18),
% 0.19/0.44    inference(avatar_component_clause,[],[f203])).
% 0.19/0.44  fof(f929,plain,(
% 0.19/0.44    spl3_55 | ~spl3_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f846,f56,f927])).
% 0.19/0.44  fof(f56,plain,(
% 0.19/0.44    spl3_1 <=> v1_relat_1(sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.44  fof(f846,plain,(
% 0.19/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))) ) | ~spl3_1),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f58,f54])).
% 0.19/0.44  fof(f54,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 0.19/0.44    inference(definition_unfolding,[],[f46,f40])).
% 0.19/0.44  fof(f46,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f23])).
% 0.19/0.44  fof(f23,plain,(
% 0.19/0.44    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f12])).
% 0.19/0.44  fof(f12,axiom,(
% 0.19/0.44    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.19/0.44  fof(f58,plain,(
% 0.19/0.44    v1_relat_1(sK1) | ~spl3_1),
% 0.19/0.44    inference(avatar_component_clause,[],[f56])).
% 0.19/0.44  fof(f330,plain,(
% 0.19/0.44    k1_xboole_0 != k7_relat_1(sK1,k1_xboole_0) | k1_xboole_0 != k7_relat_1(sK1,sK0) | k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.19/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.44  fof(f206,plain,(
% 0.19/0.44    ~spl3_18 | ~spl3_2 | spl3_10),
% 0.19/0.44    inference(avatar_split_clause,[],[f155,f132,f62,f203])).
% 0.19/0.44  fof(f62,plain,(
% 0.19/0.44    spl3_2 <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.44  fof(f132,plain,(
% 0.19/0.44    spl3_10 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.44  fof(f155,plain,(
% 0.19/0.44    k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl3_2 | spl3_10)),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f63,f133,f36])).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f18])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(flattening,[],[f17])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f10])).
% 0.19/0.44  fof(f10,axiom,(
% 0.19/0.44    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.19/0.44  fof(f133,plain,(
% 0.19/0.44    k1_xboole_0 != k7_relat_1(sK1,sK0) | spl3_10),
% 0.19/0.44    inference(avatar_component_clause,[],[f132])).
% 0.19/0.44  fof(f63,plain,(
% 0.19/0.44    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl3_2),
% 0.19/0.44    inference(avatar_component_clause,[],[f62])).
% 0.19/0.44  fof(f166,plain,(
% 0.19/0.44    spl3_14 | ~spl3_2 | ~spl3_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f156,f84,f62,f163])).
% 0.19/0.44  fof(f163,plain,(
% 0.19/0.44    spl3_14 <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.19/0.44  fof(f84,plain,(
% 0.19/0.44    spl3_5 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.44  fof(f156,plain,(
% 0.19/0.44    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) | (~spl3_2 | ~spl3_5)),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f63,f86,f36])).
% 0.19/0.44  fof(f86,plain,(
% 0.19/0.44    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) | ~spl3_5),
% 0.19/0.44    inference(avatar_component_clause,[],[f84])).
% 0.19/0.44  fof(f148,plain,(
% 0.19/0.44    ~spl3_10 | ~spl3_11),
% 0.19/0.44    inference(avatar_split_clause,[],[f33,f136,f132])).
% 0.19/0.44  fof(f33,plain,(
% 0.19/0.44    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f27])).
% 0.19/0.44  fof(f27,plain,(
% 0.19/0.44    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 0.19/0.44  fof(f26,plain,(
% 0.19/0.44    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f25,plain,(
% 0.19/0.44    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.19/0.44    inference(flattening,[],[f24])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.19/0.44    inference(nnf_transformation,[],[f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f14])).
% 0.19/0.44  fof(f14,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.19/0.44    inference(negated_conjecture,[],[f13])).
% 0.19/0.44  fof(f13,conjecture,(
% 0.19/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.19/0.44  fof(f146,plain,(
% 0.19/0.44    spl3_12 | ~spl3_11),
% 0.19/0.44    inference(avatar_split_clause,[],[f140,f136,f143])).
% 0.19/0.44  fof(f140,plain,(
% 0.19/0.44    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) | ~spl3_11),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f138,f47])).
% 0.19/0.44  fof(f47,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.19/0.44    inference(cnf_transformation,[],[f30])).
% 0.19/0.44  fof(f138,plain,(
% 0.19/0.44    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl3_11),
% 0.19/0.44    inference(avatar_component_clause,[],[f136])).
% 0.19/0.44  fof(f139,plain,(
% 0.19/0.44    spl3_10 | spl3_11),
% 0.19/0.44    inference(avatar_split_clause,[],[f32,f136,f132])).
% 0.19/0.44  fof(f32,plain,(
% 0.19/0.44    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f27])).
% 0.19/0.44  fof(f87,plain,(
% 0.19/0.44    spl3_5 | ~spl3_4),
% 0.19/0.44    inference(avatar_split_clause,[],[f81,f78,f84])).
% 0.19/0.44  fof(f78,plain,(
% 0.19/0.44    spl3_4 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.44  fof(f81,plain,(
% 0.19/0.44    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) | ~spl3_4),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f79,f38])).
% 0.19/0.44  fof(f38,plain,(
% 0.19/0.44    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.19/0.44    inference(cnf_transformation,[],[f19])).
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.19/0.44    inference(ennf_transformation,[],[f5])).
% 0.19/0.44  fof(f5,axiom,(
% 0.19/0.44    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.19/0.44  fof(f79,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) ) | ~spl3_4),
% 0.19/0.44    inference(avatar_component_clause,[],[f78])).
% 0.19/0.44  fof(f80,plain,(
% 0.19/0.44    spl3_4 | ~spl3_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f73,f56,f78])).
% 0.19/0.44  fof(f73,plain,(
% 0.19/0.44    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) ) | ~spl3_1),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f58,f45])).
% 0.19/0.44  fof(f45,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f22])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f11])).
% 0.19/0.44  fof(f11,axiom,(
% 0.19/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.19/0.44  fof(f64,plain,(
% 0.19/0.44    spl3_2 | ~spl3_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f60,f56,f62])).
% 0.19/0.44  fof(f60,plain,(
% 0.19/0.44    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl3_1),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f58,f44])).
% 0.19/0.44  fof(f44,plain,(
% 0.19/0.44    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f21])).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f9])).
% 0.19/0.44  fof(f9,axiom,(
% 0.19/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.19/0.44  fof(f59,plain,(
% 0.19/0.44    spl3_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f31,f56])).
% 0.19/0.44  fof(f31,plain,(
% 0.19/0.44    v1_relat_1(sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f27])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (7994)------------------------------
% 0.19/0.44  % (7994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (7994)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (7994)Memory used [KB]: 11513
% 0.19/0.44  % (7994)Time elapsed: 0.030 s
% 0.19/0.44  % (7994)------------------------------
% 0.19/0.44  % (7994)------------------------------
% 0.19/0.44  % (7976)Success in time 0.095 s
%------------------------------------------------------------------------------
