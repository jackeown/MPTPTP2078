%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 396 expanded)
%              Number of leaves         :   31 ( 137 expanded)
%              Depth                    :   11
%              Number of atoms          :  334 (1358 expanded)
%              Number of equality atoms :   17 (  96 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f86,f119,f165,f187,f197,f287,f288,f289,f292,f368,f376,f405,f414,f417,f425])).

fof(f425,plain,
    ( ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f120,f78,f114])).

fof(f114,plain,
    ( spl3_5
  <=> r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f78,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f120,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | spl3_1 ),
    inference(resolution,[],[f103,f72])).

fof(f72,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f45,f69])).

fof(f69,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f45,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f103,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK0,X2)
        | ~ r1_tarski(X2,sK1) )
    | spl3_1 ),
    inference(resolution,[],[f80,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f80,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f417,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f233,f82,f114,f106])).

fof(f106,plain,
    ( spl3_3
  <=> v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f82,plain,
    ( spl3_2
  <=> r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f233,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl3_2 ),
    inference(resolution,[],[f84,f99])).

fof(f99,plain,(
    ! [X5] :
      ( r1_ordinal1(X5,sK1)
      | ~ r1_tarski(X5,sK1)
      | ~ v3_ordinal1(X5) ) ),
    inference(resolution,[],[f42,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f42,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f84,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f414,plain,
    ( ~ spl3_16
    | spl3_33
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f412,f78,f402,f194])).

fof(f194,plain,
    ( spl3_16
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f402,plain,
    ( spl3_33
  <=> r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f412,plain,
    ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f229,f232])).

fof(f232,plain,
    ( ! [X2] :
        ( r2_hidden(sK0,X2)
        | ~ r1_tarski(sK1,X2) )
    | ~ spl3_1 ),
    inference(resolution,[],[f79,f53])).

fof(f79,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),sK1) )
    | ~ spl3_1 ),
    inference(resolution,[],[f79,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f405,plain,
    ( ~ spl3_9
    | ~ spl3_33
    | spl3_5 ),
    inference(avatar_split_clause,[],[f396,f114,f402,f144])).

fof(f144,plain,
    ( spl3_9
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f396,plain,
    ( ~ r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ r1_tarski(sK0,sK1)
    | spl3_5 ),
    inference(resolution,[],[f115,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f115,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f376,plain,
    ( spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f199,f148,f144])).

fof(f148,plain,
    ( spl3_10
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f199,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f97,f41])).

fof(f41,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,(
    ! [X3] :
      ( ~ v3_ordinal1(X3)
      | ~ r1_ordinal1(X3,sK1)
      | r1_tarski(X3,sK1) ) ),
    inference(resolution,[],[f42,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f368,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f108,f93])).

fof(f93,plain,(
    v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(resolution,[],[f41,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f48,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f108,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f292,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f251,f82,f114])).

fof(f251,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(resolution,[],[f93,f97])).

fof(f289,plain,
    ( spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f191,f160,f156])).

fof(f156,plain,
    ( spl3_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f160,plain,
    ( spl3_12
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f191,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f96,f41])).

fof(f96,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r1_ordinal1(sK1,X2)
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f42,f51])).

fof(f288,plain,
    ( ~ spl3_11
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f231,f78,f156])).

fof(f231,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f79,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f287,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | spl3_12
    | spl3_10 ),
    inference(avatar_split_clause,[],[f284,f148,f160,f128,f110])).

fof(f110,plain,
    ( spl3_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f128,plain,
    ( spl3_6
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f284,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | spl3_10 ),
    inference(resolution,[],[f150,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f150,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f197,plain,
    ( spl3_16
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f192,f184,f194])).

fof(f184,plain,
    ( spl3_15
  <=> r1_ordinal1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f192,plain,
    ( ~ r1_ordinal1(sK1,sK1)
    | r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f96,f42])).

fof(f187,plain,
    ( ~ spl3_4
    | spl3_15 ),
    inference(avatar_split_clause,[],[f177,f184,f110])).

fof(f177,plain,
    ( r1_ordinal1(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(factoring,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( r1_ordinal1(sK1,X0)
      | r1_ordinal1(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f42,f50])).

fof(f165,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f130,f41])).

fof(f130,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f119,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f112,f42])).

fof(f112,plain,
    ( ~ v3_ordinal1(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f86,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f71,f82,f78])).

fof(f71,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f43,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f70,f82,f78])).

fof(f70,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f44,f69])).

fof(f44,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (16910)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.44  % (16902)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.46  % (16894)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.46  % (16902)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f426,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f85,f86,f119,f165,f187,f197,f287,f288,f289,f292,f368,f376,f405,f414,f417,f425])).
% 0.20/0.46  fof(f425,plain,(
% 0.20/0.46    ~spl3_5 | spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f120,f78,f114])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    spl3_5 <=> r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    ~r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | spl3_1),
% 0.20/0.46    inference(resolution,[],[f103,f72])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f45,f69])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f47,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f46,f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f49,f66])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f57,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f63,f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,axiom,(
% 0.20/0.46    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    ( ! [X2] : (~r2_hidden(sK0,X2) | ~r1_tarski(X2,sK1)) ) | spl3_1),
% 0.20/0.46    inference(resolution,[],[f80,f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(rectify,[],[f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    ~r2_hidden(sK0,sK1) | spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f78])).
% 0.20/0.46  fof(f417,plain,(
% 0.20/0.46    ~spl3_3 | ~spl3_5 | spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f233,f82,f114,f106])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    spl3_3 <=> v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    spl3_2 <=> r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f233,plain,(
% 0.20/0.46    ~r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) | spl3_2),
% 0.20/0.46    inference(resolution,[],[f84,f99])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    ( ! [X5] : (r1_ordinal1(X5,sK1) | ~r1_tarski(X5,sK1) | ~v3_ordinal1(X5)) )),
% 0.20/0.46    inference(resolution,[],[f42,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.46    inference(flattening,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    v3_ordinal1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.46    inference(flattening,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.46    inference(negated_conjecture,[],[f16])).
% 0.20/0.46  fof(f16,conjecture,(
% 0.20/0.46    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ~r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f82])).
% 0.20/0.46  fof(f414,plain,(
% 0.20/0.46    ~spl3_16 | spl3_33 | ~spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f412,f78,f402,f194])).
% 0.20/0.46  fof(f194,plain,(
% 0.20/0.46    spl3_16 <=> r1_tarski(sK1,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.46  fof(f402,plain,(
% 0.20/0.46    spl3_33 <=> r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.46  fof(f412,plain,(
% 0.20/0.46    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~r1_tarski(sK1,sK1) | ~spl3_1),
% 0.20/0.46    inference(resolution,[],[f229,f232])).
% 0.20/0.46  fof(f232,plain,(
% 0.20/0.46    ( ! [X2] : (r2_hidden(sK0,X2) | ~r1_tarski(sK1,X2)) ) | ~spl3_1),
% 0.20/0.46    inference(resolution,[],[f79,f53])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f78])).
% 0.20/0.46  fof(f229,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),sK1)) ) | ~spl3_1),
% 0.20/0.46    inference(resolution,[],[f79,f74])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f62,f67])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.46    inference(flattening,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.46    inference(nnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.46  fof(f405,plain,(
% 0.20/0.46    ~spl3_9 | ~spl3_33 | spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f396,f114,f402,f144])).
% 0.20/0.46  fof(f144,plain,(
% 0.20/0.46    spl3_9 <=> r1_tarski(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.46  fof(f396,plain,(
% 0.20/0.46    ~r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~r1_tarski(sK0,sK1) | spl3_5),
% 0.20/0.46    inference(resolution,[],[f115,f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    ~r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f114])).
% 0.20/0.46  fof(f376,plain,(
% 0.20/0.46    spl3_9 | ~spl3_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f199,f148,f144])).
% 0.20/0.46  fof(f148,plain,(
% 0.20/0.46    spl3_10 <=> r1_ordinal1(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.46  fof(f199,plain,(
% 0.20/0.46    ~r1_ordinal1(sK0,sK1) | r1_tarski(sK0,sK1)),
% 0.20/0.46    inference(resolution,[],[f97,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    v3_ordinal1(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f33])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    ( ! [X3] : (~v3_ordinal1(X3) | ~r1_ordinal1(X3,sK1) | r1_tarski(X3,sK1)) )),
% 0.20/0.46    inference(resolution,[],[f42,f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f368,plain,(
% 0.20/0.46    spl3_3),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f366])).
% 0.20/0.46  fof(f366,plain,(
% 0.20/0.46    $false | spl3_3),
% 0.20/0.46    inference(resolution,[],[f108,f93])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.20/0.46    inference(resolution,[],[f41,f73])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) | ~v3_ordinal1(X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f48,f69])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,axiom,(
% 0.20/0.46    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    ~v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) | spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f106])).
% 0.20/0.46  fof(f292,plain,(
% 0.20/0.46    spl3_5 | ~spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f251,f82,f114])).
% 0.20/0.46  fof(f251,plain,(
% 0.20/0.46    ~r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 0.20/0.46    inference(resolution,[],[f93,f97])).
% 0.20/0.46  fof(f289,plain,(
% 0.20/0.46    spl3_11 | ~spl3_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f191,f160,f156])).
% 0.20/0.46  fof(f156,plain,(
% 0.20/0.46    spl3_11 <=> r1_tarski(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.46  fof(f160,plain,(
% 0.20/0.46    spl3_12 <=> r1_ordinal1(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.46  fof(f191,plain,(
% 0.20/0.46    ~r1_ordinal1(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.20/0.46    inference(resolution,[],[f96,f41])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ( ! [X2] : (~v3_ordinal1(X2) | ~r1_ordinal1(sK1,X2) | r1_tarski(sK1,X2)) )),
% 0.20/0.46    inference(resolution,[],[f42,f51])).
% 0.20/0.46  fof(f288,plain,(
% 0.20/0.46    ~spl3_11 | ~spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f231,f78,f156])).
% 0.20/0.46  fof(f231,plain,(
% 0.20/0.46    ~r1_tarski(sK1,sK0) | ~spl3_1),
% 0.20/0.46    inference(resolution,[],[f79,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,axiom,(
% 0.20/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.46  fof(f287,plain,(
% 0.20/0.46    ~spl3_4 | ~spl3_6 | spl3_12 | spl3_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f284,f148,f160,f128,f110])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    spl3_4 <=> v3_ordinal1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f128,plain,(
% 0.20/0.46    spl3_6 <=> v3_ordinal1(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.46  fof(f284,plain,(
% 0.20/0.46    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | spl3_10),
% 0.20/0.46    inference(resolution,[],[f150,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.46    inference(flattening,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    ~r1_ordinal1(sK0,sK1) | spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f148])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    spl3_16 | ~spl3_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f192,f184,f194])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    spl3_15 <=> r1_ordinal1(sK1,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    ~r1_ordinal1(sK1,sK1) | r1_tarski(sK1,sK1)),
% 0.20/0.47    inference(resolution,[],[f96,f42])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    ~spl3_4 | spl3_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f177,f184,f110])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    r1_ordinal1(sK1,sK1) | ~v3_ordinal1(sK1)),
% 0.20/0.47    inference(factoring,[],[f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ( ! [X0] : (r1_ordinal1(sK1,X0) | r1_ordinal1(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(resolution,[],[f42,f50])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f164])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    $false | spl3_6),
% 0.20/0.47    inference(resolution,[],[f130,f41])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ~v3_ordinal1(sK0) | spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f128])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f118])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    $false | spl3_4),
% 0.20/0.47    inference(resolution,[],[f112,f42])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    ~v3_ordinal1(sK1) | spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f110])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl3_1 | spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f71,f82,f78])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(definition_unfolding,[],[f43,f69])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ~spl3_1 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f70,f82,f78])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ~r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(definition_unfolding,[],[f44,f69])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (16902)------------------------------
% 0.20/0.47  % (16902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16902)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (16902)Memory used [KB]: 6396
% 0.20/0.47  % (16902)Time elapsed: 0.051 s
% 0.20/0.47  % (16902)------------------------------
% 0.20/0.47  % (16902)------------------------------
% 0.20/0.47  % (16886)Success in time 0.121 s
%------------------------------------------------------------------------------
