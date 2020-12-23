%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:38 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 458 expanded)
%              Number of leaves         :   24 ( 137 expanded)
%              Depth                    :   21
%              Number of atoms          :  343 (1749 expanded)
%              Number of equality atoms :   73 ( 263 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1076,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f164,f1042,f1074])).

fof(f1074,plain,(
    spl16_1 ),
    inference(avatar_contradiction_clause,[],[f1073])).

fof(f1073,plain,
    ( $false
    | spl16_1 ),
    inference(subsumption_resolution,[],[f1068,f159])).

fof(f159,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl16_1 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl16_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f1068,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f1062,f996])).

fof(f996,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f994])).

fof(f994,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK6(X0,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f993,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f993,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK6(X2,X3),k1_xboole_0)
      | X2 = X3 ) ),
    inference(subsumption_resolution,[],[f989,f659])).

fof(f659,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f654,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X1,X3,X0] :
      ( sP3(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f654,plain,(
    ! [X15,X16] :
      ( ~ sP3(k1_xboole_0,X15,X16)
      | r2_hidden(X15,X16) ) ),
    inference(resolution,[],[f123,f169])).

fof(f169,plain,(
    ! [X0] : sP4(X0,k1_xboole_0,X0) ),
    inference(superposition,[],[f147,f85])).

fof(f85,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f147,plain,(
    ! [X0,X1] : sP4(X0,X1,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP4(X0,X1,X2) )
      & ( sP4(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP4(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f40,f39])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP3(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f123,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ sP3(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ( ~ sP3(X1,sK15(X0,X1,X2),X0)
            | ~ r2_hidden(sK15(X0,X1,X2),X2) )
          & ( sP3(X1,sK15(X0,X1,X2),X0)
            | r2_hidden(sK15(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP3(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP3(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP3(X1,sK15(X0,X1,X2),X0)
          | ~ r2_hidden(sK15(X0,X1,X2),X2) )
        & ( sP3(X1,sK15(X0,X1,X2),X0)
          | r2_hidden(sK15(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (5597)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP3(X1,X3,X0) )
            & ( sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f989,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ r2_hidden(sK6(X2,X3),X2)
      | ~ r2_hidden(sK6(X2,X3),k1_xboole_0) ) ),
    inference(resolution,[],[f94,f659])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1062,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f1059,f142])).

fof(f142,plain,(
    ! [X0] : sP1(X0,k1_relat_1(X0)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ~ sP1(X0,X1) )
      & ( sP1(X0,X1)
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> sP1(X0,X1) ) ),
    inference(definition_folding,[],[f20,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1059,plain,(
    ! [X17,X16] :
      ( ~ sP1(k1_xboole_0,X17)
      | ~ r2_hidden(X16,X17) ) ),
    inference(resolution,[],[f101,f1011])).

fof(f1011,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1008,f166])).

fof(f166,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f89,f85])).

fof(f89,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f1008,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(superposition,[],[f993,f1005])).

fof(f1005,plain,(
    ! [X0] : sK6(k1_tarski(X0),k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f999,f166])).

fof(f999,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(X0)
      | sK6(k1_tarski(X0),k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f996,f270])).

fof(f270,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f107,f144])).

fof(f144,plain,(
    ! [X0] : sP2(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP2(X0,X1) )
      & ( sP2(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP2(X0,X1) ) ),
    inference(definition_folding,[],[f9,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( ~ sP2(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ( sK13(X0,X1) != X0
            | ~ r2_hidden(sK13(X0,X1),X1) )
          & ( sK13(X0,X1) = X0
            | r2_hidden(sK13(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK13(X0,X1) != X0
          | ~ r2_hidden(sK13(X0,X1),X1) )
        & ( sK13(X0,X1) = X0
          | r2_hidden(sK13(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f101,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f55,f58,f57,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f1042,plain,(
    spl16_2 ),
    inference(avatar_split_clause,[],[f1038,f161])).

fof(f161,plain,
    ( spl16_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f1038,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f1033,f996])).

fof(f1033,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f1029,f141])).

fof(f141,plain,(
    ! [X0] : sP0(X0,k2_relat_1(X0)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f21,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1029,plain,(
    ! [X12,X11] :
      ( ~ sP0(k1_xboole_0,X12)
      | ~ r2_hidden(X11,X12) ) ),
    inference(resolution,[],[f95,f1011])).

fof(f95,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f48,f51,f50,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f164,plain,
    ( ~ spl16_1
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f83,f161,f157])).

fof(f83,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.55  % (5558)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (5537)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (5537)Refutation not found, incomplete strategy% (5537)------------------------------
% 0.20/0.55  % (5537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5550)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (5563)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (5537)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (5537)Memory used [KB]: 10746
% 0.20/0.56  % (5537)Time elapsed: 0.126 s
% 0.20/0.56  % (5537)------------------------------
% 0.20/0.56  % (5537)------------------------------
% 0.20/0.56  % (5542)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.56  % (5549)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.59  % (5540)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.59  % (5535)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.59  % (5539)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.59  % (5547)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.60  % (5538)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.61  % (5562)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.61  % (5541)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.62  % (5559)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.62  % (5561)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.62  % (5536)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.62  % (5556)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.62  % (5556)Refutation not found, incomplete strategy% (5556)------------------------------
% 0.20/0.62  % (5556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.62  % (5564)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.62  % (5552)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.63  % (5548)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.63  % (5551)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.63  % (5546)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.94/0.63  % (5553)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.94/0.63  % (5555)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.94/0.63  % (5554)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.94/0.63  % (5543)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.94/0.63  % (5557)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.94/0.63  % (5545)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.94/0.63  % (5560)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.94/0.63  % (5545)Refutation not found, incomplete strategy% (5545)------------------------------
% 1.94/0.63  % (5545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.63  % (5545)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.63  
% 1.94/0.63  % (5545)Memory used [KB]: 10618
% 1.94/0.63  % (5557)Refutation not found, incomplete strategy% (5557)------------------------------
% 1.94/0.63  % (5557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.63  % (5545)Time elapsed: 0.206 s
% 1.94/0.63  % (5545)------------------------------
% 1.94/0.63  % (5545)------------------------------
% 1.94/0.63  % (5557)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.63  
% 1.94/0.63  % (5557)Memory used [KB]: 10746
% 1.94/0.63  % (5557)Time elapsed: 0.207 s
% 1.94/0.63  % (5557)------------------------------
% 1.94/0.63  % (5557)------------------------------
% 1.94/0.63  % (5544)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.94/0.64  % (5543)Refutation not found, incomplete strategy% (5543)------------------------------
% 1.94/0.64  % (5543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.64  % (5555)Refutation not found, incomplete strategy% (5555)------------------------------
% 1.94/0.64  % (5555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.64  % (5555)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.64  
% 1.94/0.64  % (5555)Memory used [KB]: 10746
% 1.94/0.64  % (5555)Time elapsed: 0.205 s
% 1.94/0.64  % (5555)------------------------------
% 1.94/0.64  % (5555)------------------------------
% 1.94/0.64  % (5556)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.64  
% 1.94/0.64  % (5556)Memory used [KB]: 1791
% 1.94/0.64  % (5556)Time elapsed: 0.196 s
% 1.94/0.64  % (5556)------------------------------
% 1.94/0.64  % (5556)------------------------------
% 2.25/0.65  % (5543)Termination reason: Refutation not found, incomplete strategy
% 2.25/0.65  
% 2.25/0.65  % (5543)Memory used [KB]: 10746
% 2.25/0.65  % (5543)Time elapsed: 0.208 s
% 2.25/0.65  % (5543)------------------------------
% 2.25/0.65  % (5543)------------------------------
% 2.25/0.69  % (5562)Refutation found. Thanks to Tanya!
% 2.25/0.69  % SZS status Theorem for theBenchmark
% 2.25/0.69  % SZS output start Proof for theBenchmark
% 2.25/0.69  fof(f1076,plain,(
% 2.25/0.69    $false),
% 2.25/0.69    inference(avatar_sat_refutation,[],[f164,f1042,f1074])).
% 2.25/0.69  fof(f1074,plain,(
% 2.25/0.69    spl16_1),
% 2.25/0.69    inference(avatar_contradiction_clause,[],[f1073])).
% 2.25/0.69  fof(f1073,plain,(
% 2.25/0.69    $false | spl16_1),
% 2.25/0.69    inference(subsumption_resolution,[],[f1068,f159])).
% 2.25/0.69  fof(f159,plain,(
% 2.25/0.69    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl16_1),
% 2.25/0.69    inference(avatar_component_clause,[],[f157])).
% 2.25/0.69  fof(f157,plain,(
% 2.25/0.69    spl16_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).
% 2.25/0.69  fof(f1068,plain,(
% 2.25/0.69    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.25/0.69    inference(resolution,[],[f1062,f996])).
% 2.25/0.69  fof(f996,plain,(
% 2.25/0.69    ( ! [X0] : (r2_hidden(sK6(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 2.25/0.69    inference(duplicate_literal_removal,[],[f994])).
% 2.25/0.69  fof(f994,plain,(
% 2.25/0.69    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = X0 | r2_hidden(sK6(X0,k1_xboole_0),X0)) )),
% 2.25/0.69    inference(resolution,[],[f993,f93])).
% 2.25/0.69  fof(f93,plain,(
% 2.25/0.69    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | X0 = X1 | r2_hidden(sK6(X0,X1),X0)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f46])).
% 2.25/0.69  fof(f46,plain,(
% 2.25/0.69    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(sK6(X0,X1),X0)) & (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0))))),
% 2.25/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).
% 2.25/0.69  fof(f45,plain,(
% 2.25/0.69    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(sK6(X0,X1),X0)) & (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0))))),
% 2.25/0.69    introduced(choice_axiom,[])).
% 2.25/0.69  fof(f44,plain,(
% 2.25/0.69    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.25/0.69    inference(nnf_transformation,[],[f29])).
% 2.25/0.69  fof(f29,plain,(
% 2.25/0.69    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.25/0.69    inference(ennf_transformation,[],[f4])).
% 2.25/0.69  fof(f4,axiom,(
% 2.25/0.69    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 2.25/0.69  fof(f993,plain,(
% 2.25/0.69    ( ! [X2,X3] : (~r2_hidden(sK6(X2,X3),k1_xboole_0) | X2 = X3) )),
% 2.25/0.69    inference(subsumption_resolution,[],[f989,f659])).
% 2.25/0.69  fof(f659,plain,(
% 2.25/0.69    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 2.25/0.69    inference(resolution,[],[f654,f128])).
% 2.25/0.69  fof(f128,plain,(
% 2.25/0.69    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f77])).
% 2.25/0.69  fof(f77,plain,(
% 2.25/0.69    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP3(X0,X1,X2)))),
% 2.25/0.69    inference(rectify,[],[f76])).
% 2.25/0.69  fof(f76,plain,(
% 2.25/0.69    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP3(X1,X3,X0)))),
% 2.25/0.69    inference(flattening,[],[f75])).
% 2.25/0.69  fof(f75,plain,(
% 2.25/0.69    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP3(X1,X3,X0)))),
% 2.25/0.69    inference(nnf_transformation,[],[f39])).
% 2.25/0.69  fof(f39,plain,(
% 2.25/0.69    ! [X1,X3,X0] : (sP3(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 2.25/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.25/0.69  fof(f654,plain,(
% 2.25/0.69    ( ! [X15,X16] : (~sP3(k1_xboole_0,X15,X16) | r2_hidden(X15,X16)) )),
% 2.25/0.69    inference(resolution,[],[f123,f169])).
% 2.25/0.69  fof(f169,plain,(
% 2.25/0.69    ( ! [X0] : (sP4(X0,k1_xboole_0,X0)) )),
% 2.25/0.69    inference(superposition,[],[f147,f85])).
% 2.25/0.69  fof(f85,plain,(
% 2.25/0.69    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.25/0.69    inference(cnf_transformation,[],[f7])).
% 2.25/0.69  fof(f7,axiom,(
% 2.25/0.69    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.25/0.69  fof(f147,plain,(
% 2.25/0.69    ( ! [X0,X1] : (sP4(X0,X1,k2_xboole_0(X0,X1))) )),
% 2.25/0.69    inference(equality_resolution,[],[f129])).
% 2.25/0.69  fof(f129,plain,(
% 2.25/0.69    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.25/0.69    inference(cnf_transformation,[],[f78])).
% 2.25/0.69  fof(f78,plain,(
% 2.25/0.69    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP4(X0,X1,X2)) & (sP4(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 2.25/0.69    inference(nnf_transformation,[],[f41])).
% 2.25/0.69  fof(f41,plain,(
% 2.25/0.69    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP4(X0,X1,X2))),
% 2.25/0.69    inference(definition_folding,[],[f2,f40,f39])).
% 2.25/0.69  fof(f40,plain,(
% 2.25/0.69    ! [X0,X1,X2] : (sP4(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP3(X1,X3,X0)))),
% 2.25/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.25/0.69  fof(f2,axiom,(
% 2.25/0.69    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.25/0.69  fof(f123,plain,(
% 2.25/0.69    ( ! [X4,X2,X0,X1] : (~sP4(X0,X1,X2) | ~sP3(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f74])).
% 2.25/0.69  fof(f74,plain,(
% 2.25/0.69    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ((~sP3(X1,sK15(X0,X1,X2),X0) | ~r2_hidden(sK15(X0,X1,X2),X2)) & (sP3(X1,sK15(X0,X1,X2),X0) | r2_hidden(sK15(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP3(X1,X4,X0)) & (sP3(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 2.25/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f72,f73])).
% 2.25/0.69  fof(f73,plain,(
% 2.25/0.69    ! [X2,X1,X0] : (? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP3(X1,sK15(X0,X1,X2),X0) | ~r2_hidden(sK15(X0,X1,X2),X2)) & (sP3(X1,sK15(X0,X1,X2),X0) | r2_hidden(sK15(X0,X1,X2),X2))))),
% 2.25/0.69    introduced(choice_axiom,[])).
% 2.25/0.70  % (5597)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.59/0.70  fof(f72,plain,(
% 2.59/0.70    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP3(X1,X4,X0)) & (sP3(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 2.59/0.70    inference(rectify,[],[f71])).
% 2.59/0.70  fof(f71,plain,(
% 2.59/0.70    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP3(X1,X3,X0)) & (sP3(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP4(X0,X1,X2)))),
% 2.59/0.70    inference(nnf_transformation,[],[f40])).
% 2.59/0.70  fof(f989,plain,(
% 2.59/0.70    ( ! [X2,X3] : (X2 = X3 | ~r2_hidden(sK6(X2,X3),X2) | ~r2_hidden(sK6(X2,X3),k1_xboole_0)) )),
% 2.59/0.70    inference(resolution,[],[f94,f659])).
% 2.59/0.70  fof(f94,plain,(
% 2.59/0.70    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK6(X0,X1),X0)) )),
% 2.59/0.70    inference(cnf_transformation,[],[f46])).
% 2.59/0.70  fof(f1062,plain,(
% 2.59/0.70    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 2.59/0.70    inference(resolution,[],[f1059,f142])).
% 2.59/0.70  fof(f142,plain,(
% 2.59/0.70    ( ! [X0] : (sP1(X0,k1_relat_1(X0))) )),
% 2.59/0.70    inference(equality_resolution,[],[f105])).
% 2.59/0.70  fof(f105,plain,(
% 2.59/0.70    ( ! [X0,X1] : (sP1(X0,X1) | k1_relat_1(X0) != X1) )),
% 2.59/0.70    inference(cnf_transformation,[],[f60])).
% 2.59/0.70  fof(f60,plain,(
% 2.59/0.70    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k1_relat_1(X0) != X1))),
% 2.59/0.70    inference(nnf_transformation,[],[f36])).
% 2.59/0.70  fof(f36,plain,(
% 2.59/0.70    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> sP1(X0,X1))),
% 2.59/0.70    inference(definition_folding,[],[f20,f35])).
% 2.59/0.70  fof(f35,plain,(
% 2.59/0.70    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.59/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.59/0.70  fof(f20,axiom,(
% 2.59/0.70    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.59/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 2.59/0.70  fof(f1059,plain,(
% 2.59/0.70    ( ! [X17,X16] : (~sP1(k1_xboole_0,X17) | ~r2_hidden(X16,X17)) )),
% 2.59/0.70    inference(resolution,[],[f101,f1011])).
% 2.59/0.70  fof(f1011,plain,(
% 2.59/0.70    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 2.59/0.70    inference(subsumption_resolution,[],[f1008,f166])).
% 2.59/0.70  fof(f166,plain,(
% 2.59/0.70    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 2.59/0.70    inference(superposition,[],[f89,f85])).
% 2.59/0.71  fof(f89,plain,(
% 2.59/0.71    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.59/0.71    inference(cnf_transformation,[],[f17])).
% 2.59/0.71  fof(f17,axiom,(
% 2.59/0.71    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.59/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 2.59/0.71  fof(f1008,plain,(
% 2.59/0.71    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | k1_xboole_0 = k1_tarski(X1)) )),
% 2.59/0.71    inference(superposition,[],[f993,f1005])).
% 2.59/0.71  fof(f1005,plain,(
% 2.59/0.71    ( ! [X0] : (sK6(k1_tarski(X0),k1_xboole_0) = X0) )),
% 2.59/0.71    inference(subsumption_resolution,[],[f999,f166])).
% 2.59/0.71  fof(f999,plain,(
% 2.59/0.71    ( ! [X0] : (k1_xboole_0 = k1_tarski(X0) | sK6(k1_tarski(X0),k1_xboole_0) = X0) )),
% 2.59/0.71    inference(resolution,[],[f996,f270])).
% 2.59/0.71  fof(f270,plain,(
% 2.59/0.71    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 2.59/0.71    inference(resolution,[],[f107,f144])).
% 2.59/0.71  fof(f144,plain,(
% 2.59/0.71    ( ! [X0] : (sP2(X0,k1_tarski(X0))) )),
% 2.59/0.71    inference(equality_resolution,[],[f111])).
% 2.59/0.71  fof(f111,plain,(
% 2.59/0.71    ( ! [X0,X1] : (sP2(X0,X1) | k1_tarski(X0) != X1) )),
% 2.59/0.71    inference(cnf_transformation,[],[f65])).
% 2.59/0.71  fof(f65,plain,(
% 2.59/0.71    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k1_tarski(X0) != X1))),
% 2.59/0.71    inference(nnf_transformation,[],[f38])).
% 2.59/0.71  fof(f38,plain,(
% 2.59/0.71    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP2(X0,X1))),
% 2.59/0.71    inference(definition_folding,[],[f9,f37])).
% 2.59/0.71  fof(f37,plain,(
% 2.59/0.71    ! [X0,X1] : (sP2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.59/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.59/0.71  fof(f9,axiom,(
% 2.59/0.71    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.59/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.59/0.71  fof(f107,plain,(
% 2.59/0.71    ( ! [X0,X3,X1] : (~sP2(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 2.59/0.71    inference(cnf_transformation,[],[f64])).
% 2.59/0.71  fof(f64,plain,(
% 2.59/0.71    ! [X0,X1] : ((sP2(X0,X1) | ((sK13(X0,X1) != X0 | ~r2_hidden(sK13(X0,X1),X1)) & (sK13(X0,X1) = X0 | r2_hidden(sK13(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP2(X0,X1)))),
% 2.59/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f62,f63])).
% 2.59/0.71  fof(f63,plain,(
% 2.59/0.71    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK13(X0,X1) != X0 | ~r2_hidden(sK13(X0,X1),X1)) & (sK13(X0,X1) = X0 | r2_hidden(sK13(X0,X1),X1))))),
% 2.59/0.71    introduced(choice_axiom,[])).
% 2.59/0.71  fof(f62,plain,(
% 2.59/0.71    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP2(X0,X1)))),
% 2.59/0.71    inference(rectify,[],[f61])).
% 2.59/0.71  fof(f61,plain,(
% 2.59/0.71    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP2(X0,X1)))),
% 2.59/0.71    inference(nnf_transformation,[],[f37])).
% 2.59/0.71  fof(f101,plain,(
% 2.59/0.71    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1) | ~sP1(X0,X1)) )),
% 2.59/0.71    inference(cnf_transformation,[],[f59])).
% 2.59/0.71  fof(f59,plain,(
% 2.59/0.71    ! [X0,X1] : ((sP1(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1))) | ~sP1(X0,X1)))),
% 2.59/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f55,f58,f57,f56])).
% 2.59/0.71  fof(f56,plain,(
% 2.59/0.71    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 2.59/0.71    introduced(choice_axiom,[])).
% 2.59/0.71  fof(f57,plain,(
% 2.59/0.71    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0))),
% 2.59/0.71    introduced(choice_axiom,[])).
% 2.59/0.71  fof(f58,plain,(
% 2.59/0.71    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0))),
% 2.59/0.71    introduced(choice_axiom,[])).
% 2.59/0.71  fof(f55,plain,(
% 2.59/0.71    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | ~sP1(X0,X1)))),
% 2.59/0.71    inference(rectify,[],[f54])).
% 2.59/0.71  fof(f54,plain,(
% 2.59/0.71    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 2.59/0.71    inference(nnf_transformation,[],[f35])).
% 2.59/0.71  fof(f1042,plain,(
% 2.59/0.71    spl16_2),
% 2.59/0.71    inference(avatar_split_clause,[],[f1038,f161])).
% 2.59/0.71  fof(f161,plain,(
% 2.59/0.71    spl16_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.59/0.71    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).
% 2.59/0.71  fof(f1038,plain,(
% 2.59/0.71    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.59/0.71    inference(resolution,[],[f1033,f996])).
% 2.59/0.71  fof(f1033,plain,(
% 2.59/0.71    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 2.59/0.71    inference(resolution,[],[f1029,f141])).
% 2.59/0.71  fof(f141,plain,(
% 2.59/0.71    ( ! [X0] : (sP0(X0,k2_relat_1(X0))) )),
% 2.59/0.71    inference(equality_resolution,[],[f99])).
% 2.59/0.71  fof(f99,plain,(
% 2.59/0.71    ( ! [X0,X1] : (sP0(X0,X1) | k2_relat_1(X0) != X1) )),
% 2.59/0.71    inference(cnf_transformation,[],[f53])).
% 2.59/0.71  fof(f53,plain,(
% 2.59/0.71    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k2_relat_1(X0) != X1))),
% 2.59/0.71    inference(nnf_transformation,[],[f34])).
% 2.59/0.71  fof(f34,plain,(
% 2.59/0.71    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> sP0(X0,X1))),
% 2.59/0.71    inference(definition_folding,[],[f21,f33])).
% 2.59/0.71  fof(f33,plain,(
% 2.59/0.71    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.59/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.59/0.71  fof(f21,axiom,(
% 2.59/0.71    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.59/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 2.59/0.71  fof(f1029,plain,(
% 2.59/0.71    ( ! [X12,X11] : (~sP0(k1_xboole_0,X12) | ~r2_hidden(X11,X12)) )),
% 2.59/0.71    inference(resolution,[],[f95,f1011])).
% 2.59/0.71  fof(f95,plain,(
% 2.59/0.71    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | ~sP0(X0,X1)) )),
% 2.59/0.71    inference(cnf_transformation,[],[f52])).
% 2.59/0.71  fof(f52,plain,(
% 2.59/0.71    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 2.59/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f48,f51,f50,f49])).
% 2.59/0.71  fof(f49,plain,(
% 2.59/0.71    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 2.59/0.71    introduced(choice_axiom,[])).
% 2.59/0.71  fof(f50,plain,(
% 2.59/0.71    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0))),
% 2.59/0.71    introduced(choice_axiom,[])).
% 2.59/0.71  fof(f51,plain,(
% 2.59/0.71    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0))),
% 2.59/0.71    introduced(choice_axiom,[])).
% 2.59/0.71  fof(f48,plain,(
% 2.59/0.71    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 2.59/0.71    inference(rectify,[],[f47])).
% 2.59/0.71  fof(f47,plain,(
% 2.59/0.71    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 2.59/0.71    inference(nnf_transformation,[],[f33])).
% 2.59/0.71  fof(f164,plain,(
% 2.59/0.71    ~spl16_1 | ~spl16_2),
% 2.59/0.71    inference(avatar_split_clause,[],[f83,f161,f157])).
% 2.59/0.71  fof(f83,plain,(
% 2.59/0.71    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.59/0.71    inference(cnf_transformation,[],[f25])).
% 2.59/0.71  fof(f25,plain,(
% 2.59/0.71    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.59/0.71    inference(ennf_transformation,[],[f23])).
% 2.59/0.71  fof(f23,negated_conjecture,(
% 2.59/0.71    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 2.59/0.71    inference(negated_conjecture,[],[f22])).
% 2.59/0.71  fof(f22,conjecture,(
% 2.59/0.71    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.59/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.59/0.71  % SZS output end Proof for theBenchmark
% 2.59/0.71  % (5562)------------------------------
% 2.59/0.71  % (5562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.71  % (5562)Termination reason: Refutation
% 2.59/0.71  
% 2.59/0.71  % (5562)Memory used [KB]: 6780
% 2.59/0.71  % (5562)Time elapsed: 0.268 s
% 2.59/0.71  % (5562)------------------------------
% 2.59/0.71  % (5562)------------------------------
% 2.59/0.71  % (5534)Success in time 0.352 s
%------------------------------------------------------------------------------
