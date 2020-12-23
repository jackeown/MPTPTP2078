%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0562+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  98 expanded)
%              Number of leaves         :   14 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :  198 ( 327 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f37,f45,f50,f55,f67,f71,f75,f82,f116,f126,f132])).

fof(f132,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f130,f29])).

fof(f29,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl10_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f130,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl10_2
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f129,f33])).

fof(f33,plain,
    ( r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl10_2
  <=> r2_hidden(sK0,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f129,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | ~ spl10_10
    | ~ spl10_21 ),
    inference(resolution,[],[f125,f66])).

fof(f66,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(sK5(X0,X1,X3),X1)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl10_10
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

% (16649)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f125,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK2,X0,sK0),sK1)
        | ~ r2_hidden(sK0,k10_relat_1(sK2,X0)) )
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl10_21
  <=> ! [X0] :
        ( ~ r2_hidden(sK0,k10_relat_1(sK2,X0))
        | ~ r2_hidden(sK5(sK2,X0,sK0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f126,plain,
    ( spl10_21
    | ~ spl10_7
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f118,f114,f53,f124])).

fof(f53,plain,
    ( spl10_7
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(k4_tarski(sK0,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f114,plain,
    ( spl10_19
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),sK2)
        | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k10_relat_1(sK2,X0))
        | ~ r2_hidden(sK5(sK2,X0,sK0),sK1) )
    | ~ spl10_7
    | ~ spl10_19 ),
    inference(resolution,[],[f115,f54])).

fof(f54,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(sK0,X3),sK2)
        | ~ r2_hidden(X3,sK1) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),sK2)
        | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) )
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl10_19
    | ~ spl10_1
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f88,f73,f28,f114])).

fof(f73,plain,
    ( spl10_12
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),sK2)
        | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) )
    | ~ spl10_1
    | ~ spl10_12 ),
    inference(resolution,[],[f74,f29])).

fof(f74,plain,
    ( ! [X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) )
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f73])).

fof(f82,plain,
    ( ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_11 ),
    inference(unit_resulting_resolution,[],[f29,f36,f46,f44,f70])).

fof(f70,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k10_relat_1(X0,X1)) )
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl10_11
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f44,plain,
    ( r2_hidden(k4_tarski(sK0,sK3),sK2)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl10_5
  <=> r2_hidden(k4_tarski(sK0,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f46,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(sK2,sK1))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f36,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl10_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f75,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f24,f73])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f71,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f22,f69])).

fof(f22,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f67,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f23,f65])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f55,plain,
    ( spl10_7
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f51,f48,f53])).

fof(f48,plain,
    ( spl10_6
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(k4_tarski(sK0,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f51,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(k4_tarski(sK0,X3),sK2) )
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f49,f26])).

fof(f26,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f49,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(k4_tarski(sK0,X3),sK2) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f50,plain,
    ( ~ spl10_2
    | spl10_6 ),
    inference(avatar_split_clause,[],[f7,f48,f32])).

fof(f7,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(sK0,X3),sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(sK0,k10_relat_1(sK2,sK1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <~> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k10_relat_1(X2,X1))
        <=> ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f45,plain,
    ( spl10_2
    | spl10_5 ),
    inference(avatar_split_clause,[],[f9,f43,f32])).

fof(f9,plain,
    ( r2_hidden(k4_tarski(sK0,sK3),sK2)
    | r2_hidden(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,
    ( spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f10,f35,f32])).

fof(f10,plain,
    ( r2_hidden(sK3,sK1)
    | r2_hidden(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f30,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f11,f28])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
