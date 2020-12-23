%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0914+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:53 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 118 expanded)
%              Number of leaves         :   11 (  41 expanded)
%              Depth                    :   17
%              Number of atoms          :  234 ( 411 expanded)
%              Number of equality atoms :   48 (  99 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f98,f101,f106,f120,f125,f128,f131])).

fof(f131,plain,
    ( ~ spl12_2
    | spl12_8 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl12_2
    | spl12_8 ),
    inference(unit_resulting_resolution,[],[f81,f119,f7])).

fof(f7,plain,(
    ! [X4] :
      ( r2_hidden(sK4(X4),sK1)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_zfmisc_1(X1,X2,X3) != X0
      & ! [X4] :
          ( r2_hidden(X4,X0)
        <=> ? [X5,X6,X7] :
              ( k3_mcart_1(X5,X6,X7) = X4
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ! [X4] :
            ( r2_hidden(X4,X0)
          <=> ? [X5,X6,X7] :
                ( k3_mcart_1(X5,X6,X7) = X4
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) ) )
       => k3_zfmisc_1(X1,X2,X3) = X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( r2_hidden(X4,X0)
        <=> ? [X5,X6,X7] :
              ( k3_mcart_1(X5,X6,X7) = X4
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) ) )
     => k3_zfmisc_1(X1,X2,X3) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_mcart_1)).

fof(f119,plain,
    ( ~ r2_hidden(sK4(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK1)
    | spl12_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl12_8
  <=> r2_hidden(sK4(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f81,plain,
    ( r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl12_2
  <=> r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f128,plain,
    ( ~ spl12_2
    | spl12_7 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl12_2
    | spl12_7 ),
    inference(unit_resulting_resolution,[],[f81,f115,f8])).

fof(f8,plain,(
    ! [X4] :
      ( r2_hidden(sK5(X4),sK2)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f115,plain,
    ( ~ r2_hidden(sK5(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK2)
    | spl12_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl12_7
  <=> r2_hidden(sK5(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f125,plain,
    ( ~ spl12_2
    | spl12_6 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl12_2
    | spl12_6 ),
    inference(unit_resulting_resolution,[],[f81,f111,f9])).

fof(f9,plain,(
    ! [X4] :
      ( r2_hidden(sK6(X4),sK3)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f111,plain,
    ( ~ r2_hidden(sK6(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK3)
    | spl12_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl12_6
  <=> r2_hidden(sK6(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

% (32635)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f120,plain,
    ( ~ spl12_6
    | ~ spl12_2
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f107,f104,f117,f113,f79,f109])).

fof(f104,plain,
    ( spl12_5
  <=> ! [X0] :
        ( sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0) != X0
        | ~ r2_hidden(sK4(X0),sK1)
        | ~ r2_hidden(sK5(X0),sK2)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK6(X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f107,plain,
    ( ~ r2_hidden(sK4(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK1)
    | ~ r2_hidden(sK5(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK2)
    | ~ r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK0)
    | ~ r2_hidden(sK6(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK3)
    | ~ spl12_5 ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,
    ( ! [X0] :
        ( sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0) != X0
        | ~ r2_hidden(sK4(X0),sK1)
        | ~ r2_hidden(sK5(X0),sK2)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK6(X0),sK3) )
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,
    ( spl12_1
    | spl12_5
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f102,f79,f104,f33])).

fof(f33,plain,
    ( spl12_1
  <=> sK0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f102,plain,
    ( ! [X0] :
        ( sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0) != X0
        | ~ r2_hidden(sK6(X0),sK3)
        | sK0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK5(X0),sK2)
        | ~ r2_hidden(sK4(X0),sK1) )
    | ~ spl12_2 ),
    inference(resolution,[],[f81,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK7(k2_zfmisc_1(X2,X3),X1,X4),X4)
      | sK7(k2_zfmisc_1(X2,X3),X1,X4) != X0
      | ~ r2_hidden(sK6(X0),X1)
      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1) = X4
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK5(X0),X3)
      | ~ r2_hidden(sK4(X0),X2) ) ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X1)
      | ~ r2_hidden(sK6(X0),X2)
      | sK7(X1,X2,X3) != X0
      | ~ r2_hidden(sK7(X1,X2,X3),X3)
      | k2_zfmisc_1(X1,X2) = X3
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f15,f25])).

fof(f25,plain,(
    ! [X4] :
      ( k4_tarski(k4_tarski(sK4(X4),sK5(X4)),sK6(X4)) = X4
      | ~ r2_hidden(X4,sK0) ) ),
    inference(definition_unfolding,[],[f10,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f10,plain,(
    ! [X4] :
      ( k3_mcart_1(sK4(X4),sK5(X4),sK6(X4)) = X4
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( k4_tarski(X4,X5) != sK7(X0,X1,X2)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f101,plain,
    ( spl12_1
    | spl12_2
    | spl12_4 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl12_1
    | spl12_2
    | spl12_4 ),
    inference(unit_resulting_resolution,[],[f35,f80,f97,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f97,plain,
    ( ~ r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK3)
    | spl12_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl12_4
  <=> r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f80,plain,
    ( ~ r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK0)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f35,plain,
    ( sK0 != k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f98,plain,
    ( spl12_1
    | ~ spl12_4
    | spl12_2 ),
    inference(avatar_split_clause,[],[f88,f79,f95,f33])).

fof(f88,plain,
    ( ~ r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK3)
    | sK0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)
    | spl12_2 ),
    inference(resolution,[],[f80,f68])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,sK0),sK0)
      | ~ r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),X0,sK0),sK3)
      | sK0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0) ) ),
    inference(factoring,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,X1),sK0)
      | ~ r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),X0,X1),sK3)
      | r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,X1),X1)
      | k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),X0,X1),sK3)
      | r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,X1),sK0)
      | r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,X1),X1)
      | k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0) = X1
      | r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,X1),X1)
      | k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0) = X1 ) ),
    inference(resolution,[],[f50,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK10(X3,X4,X5),k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(sK11(X3,X4,X5),sK3)
      | r2_hidden(sK7(X3,X4,X5),sK0)
      | r2_hidden(sK7(X3,X4,X5),X5)
      | k2_zfmisc_1(X3,X4) = X5 ) ),
    inference(superposition,[],[f47,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( sK7(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2))
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK0)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(duplicate_literal_removal,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(k4_tarski(X1,X0),sK0)
      | ~ r2_hidden(X1,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f45,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X2,sK2,X0),sK1)
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK2)) ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(sK8(X2,sK2,X0),sK1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK2)) ) ),
    inference(resolution,[],[f39,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK9(X0,X1,X2),sK2)
      | r2_hidden(k4_tarski(X2,X3),sK0)
      | ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(sK8(X0,X1,X2),sK1)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f26,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(k4_tarski(k4_tarski(X5,X6),X7),sK0)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | k4_tarski(k4_tarski(X5,X6),X7) != X4
      | r2_hidden(X4,sK0) ) ),
    inference(definition_unfolding,[],[f11,f13])).

fof(f11,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | k3_mcart_1(X5,X6,X7) != X4
      | r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f23,f33])).

fof(f23,plain,(
    sK0 != k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f12,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f12,plain,(
    sK0 != k3_zfmisc_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
