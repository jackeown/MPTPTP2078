%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:37 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.34s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_mcart_1)).

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

% (30753)Refutation not found, incomplete strategy% (30753)------------------------------
% (30753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30753)Termination reason: Refutation not found, incomplete strategy

% (30753)Memory used [KB]: 10618
% (30753)Time elapsed: 0.132 s
% (30753)------------------------------
% (30753)------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

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

% (30764)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f12,plain,(
    sK0 != k3_zfmisc_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (30742)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (30759)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.52  % (30750)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.52  % (30759)Refutation found. Thanks to Tanya!
% 1.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % (30737)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.53  % (30738)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.53  % (30736)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.54  % (30739)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.54  % (30741)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.54  % (30748)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (30760)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.54  % (30749)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.54  % (30756)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.54  % (30765)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  % (30755)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.54  % (30745)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.54  % (30753)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.54  % (30751)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f132,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(avatar_sat_refutation,[],[f36,f98,f101,f106,f120,f125,f128,f131])).
% 1.34/0.54  fof(f131,plain,(
% 1.34/0.54    ~spl12_2 | spl12_8),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f129])).
% 1.34/0.54  fof(f129,plain,(
% 1.34/0.54    $false | (~spl12_2 | spl12_8)),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f81,f119,f7])).
% 1.34/0.54  fof(f7,plain,(
% 1.34/0.54    ( ! [X4] : (r2_hidden(sK4(X4),sK1) | ~r2_hidden(X4,sK0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,plain,(
% 1.34/0.54    ? [X0,X1,X2,X3] : (k3_zfmisc_1(X1,X2,X3) != X0 & ! [X4] : (r2_hidden(X4,X0) <=> ? [X5,X6,X7] : (k3_mcart_1(X5,X6,X7) = X4 & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1,X2,X3] : (! [X4] : (r2_hidden(X4,X0) <=> ? [X5,X6,X7] : (k3_mcart_1(X5,X6,X7) = X4 & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1))) => k3_zfmisc_1(X1,X2,X3) = X0)),
% 1.34/0.54    inference(negated_conjecture,[],[f4])).
% 1.34/0.54  fof(f4,conjecture,(
% 1.34/0.54    ! [X0,X1,X2,X3] : (! [X4] : (r2_hidden(X4,X0) <=> ? [X5,X6,X7] : (k3_mcart_1(X5,X6,X7) = X4 & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1))) => k3_zfmisc_1(X1,X2,X3) = X0)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_mcart_1)).
% 1.34/0.54  fof(f119,plain,(
% 1.34/0.54    ~r2_hidden(sK4(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK1) | spl12_8),
% 1.34/0.54    inference(avatar_component_clause,[],[f117])).
% 1.34/0.54  fof(f117,plain,(
% 1.34/0.54    spl12_8 <=> r2_hidden(sK4(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK1)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.34/0.54  fof(f81,plain,(
% 1.34/0.54    r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK0) | ~spl12_2),
% 1.34/0.54    inference(avatar_component_clause,[],[f79])).
% 1.34/0.54  fof(f79,plain,(
% 1.34/0.54    spl12_2 <=> r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.34/0.54  fof(f128,plain,(
% 1.34/0.54    ~spl12_2 | spl12_7),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f126])).
% 1.34/0.54  fof(f126,plain,(
% 1.34/0.54    $false | (~spl12_2 | spl12_7)),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f81,f115,f8])).
% 1.34/0.54  fof(f8,plain,(
% 1.34/0.54    ( ! [X4] : (r2_hidden(sK5(X4),sK2) | ~r2_hidden(X4,sK0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f115,plain,(
% 1.34/0.54    ~r2_hidden(sK5(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK2) | spl12_7),
% 1.34/0.54    inference(avatar_component_clause,[],[f113])).
% 1.34/0.54  fof(f113,plain,(
% 1.34/0.54    spl12_7 <=> r2_hidden(sK5(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK2)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 1.34/0.54  fof(f125,plain,(
% 1.34/0.54    ~spl12_2 | spl12_6),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f123])).
% 1.34/0.54  fof(f123,plain,(
% 1.34/0.54    $false | (~spl12_2 | spl12_6)),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f81,f111,f9])).
% 1.34/0.54  fof(f9,plain,(
% 1.34/0.54    ( ! [X4] : (r2_hidden(sK6(X4),sK3) | ~r2_hidden(X4,sK0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f111,plain,(
% 1.34/0.54    ~r2_hidden(sK6(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK3) | spl12_6),
% 1.34/0.54    inference(avatar_component_clause,[],[f109])).
% 1.34/0.54  fof(f109,plain,(
% 1.34/0.54    spl12_6 <=> r2_hidden(sK6(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK3)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 1.34/0.54  fof(f120,plain,(
% 1.34/0.54    ~spl12_6 | ~spl12_2 | ~spl12_7 | ~spl12_8 | ~spl12_5),
% 1.34/0.54    inference(avatar_split_clause,[],[f107,f104,f117,f113,f79,f109])).
% 1.34/0.54  fof(f104,plain,(
% 1.34/0.54    spl12_5 <=> ! [X0] : (sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0) != X0 | ~r2_hidden(sK4(X0),sK1) | ~r2_hidden(sK5(X0),sK2) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK6(X0),sK3))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 1.34/0.54  fof(f107,plain,(
% 1.34/0.54    ~r2_hidden(sK4(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK1) | ~r2_hidden(sK5(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK2) | ~r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK0) | ~r2_hidden(sK6(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0)),sK3) | ~spl12_5),
% 1.34/0.54    inference(equality_resolution,[],[f105])).
% 1.34/0.54  % (30753)Refutation not found, incomplete strategy% (30753)------------------------------
% 1.34/0.54  % (30753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (30753)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (30753)Memory used [KB]: 10618
% 1.34/0.54  % (30753)Time elapsed: 0.132 s
% 1.34/0.54  % (30753)------------------------------
% 1.34/0.54  % (30753)------------------------------
% 1.34/0.54  fof(f105,plain,(
% 1.34/0.54    ( ! [X0] : (sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0) != X0 | ~r2_hidden(sK4(X0),sK1) | ~r2_hidden(sK5(X0),sK2) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK6(X0),sK3)) ) | ~spl12_5),
% 1.34/0.54    inference(avatar_component_clause,[],[f104])).
% 1.34/0.54  fof(f106,plain,(
% 1.34/0.54    spl12_1 | spl12_5 | ~spl12_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f102,f79,f104,f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    spl12_1 <=> sK0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.34/0.54  fof(f102,plain,(
% 1.34/0.54    ( ! [X0] : (sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0) != X0 | ~r2_hidden(sK6(X0),sK3) | sK0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK5(X0),sK2) | ~r2_hidden(sK4(X0),sK1)) ) | ~spl12_2),
% 1.34/0.54    inference(resolution,[],[f81,f63])).
% 1.34/0.54  fof(f63,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK7(k2_zfmisc_1(X2,X3),X1,X4),X4) | sK7(k2_zfmisc_1(X2,X3),X1,X4) != X0 | ~r2_hidden(sK6(X0),X1) | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1) = X4 | ~r2_hidden(X0,sK0) | ~r2_hidden(sK5(X0),X3) | ~r2_hidden(sK4(X0),X2)) )),
% 1.34/0.54    inference(resolution,[],[f37,f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.34/0.54    inference(equality_resolution,[],[f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.34/0.54    inference(equality_resolution,[],[f22])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X1) | ~r2_hidden(sK6(X0),X2) | sK7(X1,X2,X3) != X0 | ~r2_hidden(sK7(X1,X2,X3),X3) | k2_zfmisc_1(X1,X2) = X3 | ~r2_hidden(X0,sK0)) )),
% 1.34/0.54    inference(superposition,[],[f15,f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ( ! [X4] : (k4_tarski(k4_tarski(sK4(X4),sK5(X4)),sK6(X4)) = X4 | ~r2_hidden(X4,sK0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f10,f13])).
% 1.34/0.54  fof(f13,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f2])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.34/0.54  fof(f10,plain,(
% 1.34/0.54    ( ! [X4] : (k3_mcart_1(sK4(X4),sK5(X4),sK6(X4)) = X4 | ~r2_hidden(X4,sK0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f15,plain,(
% 1.34/0.54    ( ! [X4,X2,X0,X5,X1] : (k4_tarski(X4,X5) != sK7(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0) | ~r2_hidden(sK7(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f101,plain,(
% 1.34/0.54    spl12_1 | spl12_2 | spl12_4),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f99])).
% 1.34/0.54  fof(f99,plain,(
% 1.34/0.54    $false | (spl12_1 | spl12_2 | spl12_4)),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f35,f80,f97,f17])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK11(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f97,plain,(
% 1.34/0.54    ~r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK3) | spl12_4),
% 1.34/0.54    inference(avatar_component_clause,[],[f95])).
% 1.34/0.54  fof(f95,plain,(
% 1.34/0.54    spl12_4 <=> r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK3)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.34/0.54  % (30764)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  fof(f80,plain,(
% 1.34/0.54    ~r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK0) | spl12_2),
% 1.34/0.54    inference(avatar_component_clause,[],[f79])).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    sK0 != k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) | spl12_1),
% 1.34/0.54    inference(avatar_component_clause,[],[f33])).
% 1.34/0.54  fof(f98,plain,(
% 1.34/0.54    spl12_1 | ~spl12_4 | spl12_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f88,f79,f95,f33])).
% 1.34/0.54  fof(f88,plain,(
% 1.34/0.54    ~r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),sK3,sK0),sK3) | sK0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) | spl12_2),
% 1.34/0.54    inference(resolution,[],[f80,f68])).
% 1.34/0.54  fof(f68,plain,(
% 1.34/0.54    ( ! [X0] : (r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,sK0),sK0) | ~r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),X0,sK0),sK3) | sK0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0)) )),
% 1.34/0.54    inference(factoring,[],[f67])).
% 1.34/0.54  fof(f67,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,X1),sK0) | ~r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),X0,X1),sK3) | r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,X1),X1) | k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0) = X1) )),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f66])).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(sK11(k2_zfmisc_1(sK1,sK2),X0,X1),sK3) | r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,X1),sK0) | r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,X1),X1) | k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0) = X1 | r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),X0,X1),X1) | k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),X0) = X1) )),
% 1.34/0.54    inference(resolution,[],[f50,f16])).
% 1.34/0.54  fof(f16,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f50,plain,(
% 1.34/0.54    ( ! [X4,X5,X3] : (~r2_hidden(sK10(X3,X4,X5),k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK11(X3,X4,X5),sK3) | r2_hidden(sK7(X3,X4,X5),sK0) | r2_hidden(sK7(X3,X4,X5),X5) | k2_zfmisc_1(X3,X4) = X5) )),
% 1.34/0.54    inference(superposition,[],[f47,f18])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (sK7(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)) | r2_hidden(sK7(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK0) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,k2_zfmisc_1(sK1,sK2))) )),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f46])).
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(X0,sK3) | r2_hidden(k4_tarski(X1,X0),sK0) | ~r2_hidden(X1,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X1,k2_zfmisc_1(sK1,sK2))) )),
% 1.34/0.54    inference(resolution,[],[f45,f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.34/0.54    inference(equality_resolution,[],[f19])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK8(X2,sK2,X0),sK1) | ~r2_hidden(X1,sK3) | r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(X0,k2_zfmisc_1(X2,sK2))) )),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f44])).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(X1,sK3) | ~r2_hidden(sK8(X2,sK2,X0),sK1) | ~r2_hidden(X0,k2_zfmisc_1(X2,sK2)) | ~r2_hidden(X0,k2_zfmisc_1(X2,sK2))) )),
% 1.34/0.54    inference(resolution,[],[f39,f30])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.34/0.54    inference(equality_resolution,[],[f20])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK9(X0,X1,X2),sK2) | r2_hidden(k4_tarski(X2,X3),sK0) | ~r2_hidden(X3,sK3) | ~r2_hidden(sK8(X0,X1,X2),sK1) | ~r2_hidden(X2,k2_zfmisc_1(X0,X1))) )),
% 1.34/0.54    inference(superposition,[],[f26,f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3 | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.34/0.54    inference(equality_resolution,[],[f21])).
% 1.34/0.54  fof(f21,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ( ! [X6,X7,X5] : (r2_hidden(k4_tarski(k4_tarski(X5,X6),X7),sK0) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | ~r2_hidden(X5,sK1)) )),
% 1.34/0.54    inference(equality_resolution,[],[f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ( ! [X6,X4,X7,X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | k4_tarski(k4_tarski(X5,X6),X7) != X4 | r2_hidden(X4,sK0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f11,f13])).
% 1.34/0.54  fof(f11,plain,(
% 1.34/0.54    ( ! [X6,X4,X7,X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | k3_mcart_1(X5,X6,X7) != X4 | r2_hidden(X4,sK0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ~spl12_1),
% 1.34/0.54    inference(avatar_split_clause,[],[f23,f33])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    sK0 != k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),
% 1.34/0.54    inference(definition_unfolding,[],[f12,f14])).
% 1.34/0.54  fof(f14,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.34/0.54  fof(f12,plain,(
% 1.34/0.54    sK0 != k3_zfmisc_1(sK1,sK2,sK3)),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (30759)------------------------------
% 1.34/0.54  % (30759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (30759)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (30759)Memory used [KB]: 11001
% 1.34/0.54  % (30759)Time elapsed: 0.121 s
% 1.34/0.54  % (30759)------------------------------
% 1.34/0.54  % (30759)------------------------------
% 1.34/0.54  % (30735)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.54  % (30743)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.54  % (30732)Success in time 0.186 s
%------------------------------------------------------------------------------
