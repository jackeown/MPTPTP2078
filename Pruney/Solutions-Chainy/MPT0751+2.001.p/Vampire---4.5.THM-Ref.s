%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 203 expanded)
%              Number of leaves         :   25 (  82 expanded)
%              Depth                    :   17
%              Number of atoms          :  405 ( 852 expanded)
%              Number of equality atoms :   38 ( 112 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f315,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f70,f74,f75,f79,f84,f91,f127,f130,f156,f178,f234,f247,f299])).

fof(f299,plain,
    ( ~ spl3_5
    | spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f295,f122,f62,f77])).

fof(f77,plain,
    ( spl3_5
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f62,plain,
    ( spl3_2
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f122,plain,
    ( spl3_10
  <=> r2_hidden(k1_ordinal1(sK2(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

% (13311)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (13310)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (13309)Refutation not found, incomplete strategy% (13309)------------------------------
% (13309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13309)Termination reason: Refutation not found, incomplete strategy

% (13309)Memory used [KB]: 10618
% (13309)Time elapsed: 0.079 s
% (13309)------------------------------
% (13309)------------------------------
fof(f295,plain,
    ( v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f123,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
            & r2_hidden(sK2(X0),X0)
            & v3_ordinal1(sK2(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
        & r2_hidden(sK2(X0),X0)
        & v3_ordinal1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f123,plain,
    ( r2_hidden(k1_ordinal1(sK2(sK0)),sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f247,plain,
    ( ~ spl3_12
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f237,f145,f145])).

fof(f145,plain,
    ( spl3_12
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f237,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ spl3_12 ),
    inference(resolution,[],[f233,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f233,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f234,plain,
    ( ~ spl3_4
    | spl3_12
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f232,f176,f82,f66,f145,f72])).

fof(f72,plain,
    ( spl3_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f66,plain,
    ( spl3_3
  <=> sK0 = k1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f82,plain,
    ( spl3_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f176,plain,
    ( spl3_19
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_ordinal1(X0),sK0)
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f232,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f231,f67])).

fof(f67,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f231,plain,
    ( r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(resolution,[],[f177,f83])).

fof(f83,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_ordinal1(X0),sK0)
        | ~ v3_ordinal1(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( ~ spl3_5
    | spl3_19
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f174,f62,f176,f77])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v3_ordinal1(X0)
        | r2_hidden(k1_ordinal1(X0),sK0)
        | ~ v3_ordinal1(sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f63,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ v4_ordinal1(X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | r2_hidden(k1_ordinal1(X2),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,
    ( v4_ordinal1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f156,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f143,f119,f59,f125])).

fof(f125,plain,
    ( spl3_11
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f59,plain,
    ( spl3_1
  <=> ! [X2] :
        ( k1_ordinal1(X2) != sK0
        | ~ v3_ordinal1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f119,plain,
    ( spl3_9
  <=> sK0 = k1_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f143,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( sK0 != sK0
    | ~ v3_ordinal1(sK2(sK0))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f60,f120])).

fof(f120,plain,
    ( sK0 = k1_ordinal1(sK2(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f60,plain,
    ( ! [X2] :
        ( k1_ordinal1(X2) != sK0
        | ~ v3_ordinal1(X2) )
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f130,plain,
    ( ~ spl3_5
    | spl3_2
    | spl3_11 ),
    inference(avatar_split_clause,[],[f129,f125,f62,f77])).

fof(f129,plain,
    ( v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | spl3_11 ),
    inference(resolution,[],[f126,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v3_ordinal1(sK2(X0))
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f126,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl3_9
    | ~ spl3_5
    | spl3_10
    | ~ spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f115,f89,f125,f122,f77,f119])).

fof(f89,plain,
    ( spl3_7
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f115,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | r2_hidden(k1_ordinal1(sK2(sK0)),sK0)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_ordinal1(sK2(sK0))
    | ~ spl3_7 ),
    inference(resolution,[],[f113,f90])).

fof(f90,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | k1_ordinal1(X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = X1
      | ~ v3_ordinal1(X0)
      | r2_hidden(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f111,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(k1_ordinal1(X0))
      | k1_ordinal1(X0) = X1
      | ~ v3_ordinal1(X0)
      | r2_hidden(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f110,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(k1_ordinal1(X1))
      | ~ r2_hidden(X1,X0)
      | k1_ordinal1(X1) = X0
      | ~ v3_ordinal1(X1)
      | r2_hidden(k1_ordinal1(X1),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(X1,X0)
      | k1_ordinal1(X1) = X0
      | ~ v3_ordinal1(X1)
      | r2_hidden(k1_ordinal1(X1),X0)
      | ~ v3_ordinal1(X0)
      | ~ v1_ordinal1(k1_ordinal1(X1)) ) ),
    inference(resolution,[],[f106,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f106,plain,(
    ! [X2,X3] :
      ( r2_xboole_0(k1_ordinal1(X2),X3)
      | ~ v3_ordinal1(X3)
      | ~ r2_hidden(X2,X3)
      | k1_ordinal1(X2) = X3
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f104,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_ordinal1(X1),X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(k1_ordinal1(X1),X0)
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f98,f46])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(resolution,[],[f52,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f91,plain,
    ( ~ spl3_5
    | spl3_7
    | spl3_2 ),
    inference(avatar_split_clause,[],[f86,f62,f89,f77])).

fof(f86,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ v3_ordinal1(sK0)
    | spl3_2 ),
    inference(resolution,[],[f50,f69])).

fof(f69,plain,
    ( ~ v4_ordinal1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f50,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f80,f66,f82])).

fof(f80,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_3 ),
    inference(superposition,[],[f44,f67])).

fof(f44,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f79,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f37,f77])).

fof(f37,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ( v4_ordinal1(sK0)
        & sK0 = k1_ordinal1(sK1)
        & v3_ordinal1(sK1) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK0
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK0) ) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK0)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK0) ) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( k1_ordinal1(X1) = sK0
        & v3_ordinal1(X1) )
   => ( sK0 = k1_ordinal1(sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

fof(f75,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f38,f72,f62])).

fof(f38,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,
    ( spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f39,f72,f59])).

fof(f39,plain,(
    ! [X2] :
      ( v3_ordinal1(sK1)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f40,f66,f62])).

fof(f40,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f43,f62,f59])).

fof(f43,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (13319)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (13320)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (13312)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (13309)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (13312)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f64,f70,f74,f75,f79,f84,f91,f127,f130,f156,f178,f234,f247,f299])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ~spl3_5 | spl3_2 | ~spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f295,f122,f62,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl3_5 <=> v3_ordinal1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl3_2 <=> v4_ordinal1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl3_10 <=> r2_hidden(k1_ordinal1(sK2(sK0)),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  % (13311)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (13310)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (13309)Refutation not found, incomplete strategy% (13309)------------------------------
% 0.21/0.49  % (13309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13309)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13309)Memory used [KB]: 10618
% 0.21/0.49  % (13309)Time elapsed: 0.079 s
% 0.21/0.49  % (13309)------------------------------
% 0.21/0.49  % (13309)------------------------------
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    v4_ordinal1(sK0) | ~v3_ordinal1(sK0) | ~spl3_10),
% 0.21/0.49    inference(resolution,[],[f123,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k1_ordinal1(sK2(X0)),X0) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(rectify,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    r2_hidden(k1_ordinal1(sK2(sK0)),sK0) | ~spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ~spl3_12 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f237,f145,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    spl3_12 <=> r2_hidden(sK0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK0) | ~spl3_12),
% 0.21/0.49    inference(resolution,[],[f233,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    r2_hidden(sK0,sK0) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f145])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ~spl3_4 | spl3_12 | ~spl3_3 | ~spl3_6 | ~spl3_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f232,f176,f82,f66,f145,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl3_4 <=> v3_ordinal1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl3_3 <=> sK0 = k1_ordinal1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl3_6 <=> r2_hidden(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl3_19 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_ordinal1(X0),sK0) | ~v3_ordinal1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    r2_hidden(sK0,sK0) | ~v3_ordinal1(sK1) | (~spl3_3 | ~spl3_6 | ~spl3_19)),
% 0.21/0.49    inference(forward_demodulation,[],[f231,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    sK0 = k1_ordinal1(sK1) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    r2_hidden(k1_ordinal1(sK1),sK0) | ~v3_ordinal1(sK1) | (~spl3_6 | ~spl3_19)),
% 0.21/0.49    inference(resolution,[],[f177,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    r2_hidden(sK1,sK0) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_ordinal1(X0),sK0) | ~v3_ordinal1(X0)) ) | ~spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f176])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ~spl3_5 | spl3_19 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f174,f62,f176,f77])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v3_ordinal1(X0) | r2_hidden(k1_ordinal1(X0),sK0) | ~v3_ordinal1(sK0)) ) | ~spl3_2),
% 0.21/0.49    inference(resolution,[],[f63,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v4_ordinal1(X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | r2_hidden(k1_ordinal1(X2),X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    v4_ordinal1(sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ~spl3_11 | ~spl3_1 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f143,f119,f59,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl3_11 <=> v3_ordinal1(sK2(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_1 <=> ! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl3_9 <=> sK0 = k1_ordinal1(sK2(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ~v3_ordinal1(sK2(sK0)) | (~spl3_1 | ~spl3_9)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    sK0 != sK0 | ~v3_ordinal1(sK2(sK0)) | (~spl3_1 | ~spl3_9)),
% 0.21/0.49    inference(superposition,[],[f60,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    sK0 = k1_ordinal1(sK2(sK0)) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f119])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) ) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~spl3_5 | spl3_2 | spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f129,f125,f62,f77])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    v4_ordinal1(sK0) | ~v3_ordinal1(sK0) | spl3_11),
% 0.21/0.49    inference(resolution,[],[f126,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (v3_ordinal1(sK2(X0)) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ~v3_ordinal1(sK2(sK0)) | spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f125])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl3_9 | ~spl3_5 | spl3_10 | ~spl3_11 | ~spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f115,f89,f125,f122,f77,f119])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl3_7 <=> r2_hidden(sK2(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~v3_ordinal1(sK2(sK0)) | r2_hidden(k1_ordinal1(sK2(sK0)),sK0) | ~v3_ordinal1(sK0) | sK0 = k1_ordinal1(sK2(sK0)) | ~spl3_7),
% 0.21/0.49    inference(resolution,[],[f113,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    r2_hidden(sK2(sK0),sK0) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X0) | r2_hidden(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | k1_ordinal1(X0) = X1) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_ordinal1(X0) = X1 | ~v3_ordinal1(X0) | r2_hidden(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f111,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_ordinal1(k1_ordinal1(X0)) | k1_ordinal1(X0) = X1 | ~v3_ordinal1(X0) | r2_hidden(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f110,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_ordinal1(k1_ordinal1(X1)) | ~r2_hidden(X1,X0) | k1_ordinal1(X1) = X0 | ~v3_ordinal1(X1) | r2_hidden(k1_ordinal1(X1),X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~r2_hidden(X1,X0) | k1_ordinal1(X1) = X0 | ~v3_ordinal1(X1) | r2_hidden(k1_ordinal1(X1),X0) | ~v3_ordinal1(X0) | ~v1_ordinal1(k1_ordinal1(X1))) )),
% 0.21/0.49    inference(resolution,[],[f106,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_xboole_0(k1_ordinal1(X2),X3) | ~v3_ordinal1(X3) | ~r2_hidden(X2,X3) | k1_ordinal1(X2) = X3 | ~v3_ordinal1(X2)) )),
% 0.21/0.49    inference(resolution,[],[f104,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_ordinal1(X1),X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.49    inference(resolution,[],[f98,f46])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(k1_ordinal1(X0))) )),
% 0.21/0.49    inference(resolution,[],[f52,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~spl3_5 | spl3_7 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f86,f62,f89,f77])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    r2_hidden(sK2(sK0),sK0) | ~v3_ordinal1(sK0) | spl3_2),
% 0.21/0.49    inference(resolution,[],[f50,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~v4_ordinal1(sK0) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (v4_ordinal1(X0) | r2_hidden(sK2(X0),X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl3_6 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f80,f66,f82])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    r2_hidden(sK1,sK0) | ~spl3_3),
% 0.21/0.49    inference(superposition,[],[f44,f67])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f77])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v3_ordinal1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ((v4_ordinal1(sK0) & (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK0) & ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1)) => (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 0.21/0.49    inference(rectify,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~spl3_2 | spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f72,f62])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl3_1 | spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f72,f59])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2] : (v3_ordinal1(sK1) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ~spl3_2 | spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f66,f62])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    sK0 = k1_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl3_1 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f62,f59])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2] : (v4_ordinal1(sK0) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (13312)------------------------------
% 0.21/0.49  % (13312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13312)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (13312)Memory used [KB]: 10746
% 0.21/0.49  % (13312)Time elapsed: 0.012 s
% 0.21/0.49  % (13312)------------------------------
% 0.21/0.49  % (13312)------------------------------
% 0.21/0.49  % (13313)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (13305)Success in time 0.134 s
%------------------------------------------------------------------------------
