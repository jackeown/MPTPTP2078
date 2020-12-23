%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:22 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 450 expanded)
%              Number of leaves         :   20 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          :  342 (2060 expanded)
%              Number of equality atoms :   27 ( 102 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f77,f279,f644,f663,f1107,f1238])).

fof(f1238,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f1237])).

fof(f1237,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f1236,f1158])).

fof(f1158,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f37,f75,f78,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f78,plain,(
    v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f36,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f59,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f42,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f36,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f75,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_2
  <=> r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f37,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f1236,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f1226,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1226,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(k2_tarski(sK0,sK0),sK0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f1121,f1156,f67])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1156,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f1119,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1119,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f70,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f70,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1121,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f1107,plain,
    ( ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f1106])).

fof(f1106,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f1098,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1098,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f880,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f50,f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f880,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f840,f840,f67])).

fof(f840,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f737,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f737,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f717,f52])).

fof(f717,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK0)
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f36,f78,f711,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f711,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK0)
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f74,f277])).

fof(f277,plain,
    ( sK0 = sK1
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl3_12
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f74,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f663,plain,
    ( ~ spl3_1
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | ~ spl3_1
    | spl3_11 ),
    inference(subsumption_resolution,[],[f661,f642])).

fof(f642,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f36,f37,f273,f48])).

fof(f273,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl3_11
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f661,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f36,f37,f650,f43])).

fof(f650,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f70,f47])).

fof(f644,plain,
    ( ~ spl3_2
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f643])).

fof(f643,plain,
    ( $false
    | ~ spl3_2
    | spl3_11 ),
    inference(subsumption_resolution,[],[f642,f356])).

fof(f356,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f36,f37,f280,f43])).

fof(f280,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f164,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f164,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f112,f52])).

fof(f112,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f37,f74,f78,f48])).

fof(f279,plain,
    ( ~ spl3_11
    | spl3_12
    | spl3_1 ),
    inference(avatar_split_clause,[],[f262,f69,f275,f271])).

fof(f262,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(superposition,[],[f46,f179])).

fof(f179,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(superposition,[],[f136,f45])).

fof(f136,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f97,f46])).

fof(f97,plain,
    ( r1_tarski(sK1,sK0)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f37,f36,f83,f48])).

fof(f83,plain,
    ( r1_ordinal1(sK1,sK0)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f37,f36,f71,f43])).

fof(f71,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

% (6934)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f77,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f61,f73,f69])).

fof(f61,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f38,f59])).

fof(f38,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f60,f73,f69])).

fof(f60,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f39,f59])).

fof(f39,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:11:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.50  % (6949)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.50  % (6957)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.52  % (6953)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.52  % (6953)Refutation not found, incomplete strategy% (6953)------------------------------
% 0.23/0.52  % (6953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (6953)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (6953)Memory used [KB]: 10746
% 0.23/0.52  % (6953)Time elapsed: 0.095 s
% 0.23/0.52  % (6953)------------------------------
% 0.23/0.52  % (6953)------------------------------
% 0.23/0.52  % (6932)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.53  % (6944)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.53  % (6945)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.54  % (6937)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.54  % (6938)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.55  % (6956)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.55  % (6954)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.55  % (6931)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.55  % (6955)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.56  % (6946)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.56  % (6933)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.56  % (6948)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.56  % (6935)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.56  % (6936)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.56  % (6939)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.56  % (6951)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.57  % (6947)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.57  % (6957)Refutation found. Thanks to Tanya!
% 0.23/0.57  % SZS status Theorem for theBenchmark
% 0.23/0.57  % SZS output start Proof for theBenchmark
% 0.23/0.57  fof(f1239,plain,(
% 0.23/0.57    $false),
% 0.23/0.57    inference(avatar_sat_refutation,[],[f76,f77,f279,f644,f663,f1107,f1238])).
% 0.23/0.57  fof(f1238,plain,(
% 0.23/0.57    ~spl3_1 | spl3_2),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f1237])).
% 0.23/0.57  fof(f1237,plain,(
% 0.23/0.57    $false | (~spl3_1 | spl3_2)),
% 0.23/0.57    inference(subsumption_resolution,[],[f1236,f1158])).
% 0.23/0.57  fof(f1158,plain,(
% 0.23/0.57    r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | spl3_2),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f37,f75,f78,f43])).
% 0.23/0.57  fof(f43,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f18])).
% 0.23/0.57  fof(f18,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.23/0.57    inference(flattening,[],[f17])).
% 0.23/0.57  fof(f17,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.23/0.57    inference(ennf_transformation,[],[f10])).
% 0.23/0.57  fof(f10,axiom,(
% 0.23/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.23/0.57  fof(f78,plain,(
% 0.23/0.57    v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f36,f62])).
% 0.23/0.57  fof(f62,plain,(
% 0.23/0.57    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) | ~v3_ordinal1(X0)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f42,f59])).
% 0.23/0.57  fof(f59,plain,(
% 0.23/0.57    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 0.23/0.57    inference(definition_unfolding,[],[f41,f40])).
% 0.23/0.57  fof(f40,plain,(
% 0.23/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f6])).
% 0.23/0.57  fof(f6,axiom,(
% 0.23/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.57  fof(f41,plain,(
% 0.23/0.57    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f8])).
% 0.23/0.57  fof(f8,axiom,(
% 0.23/0.57    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.23/0.57  fof(f42,plain,(
% 0.23/0.57    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f16])).
% 0.23/0.57  fof(f16,plain,(
% 0.23/0.57    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.23/0.57    inference(ennf_transformation,[],[f11])).
% 0.23/0.57  fof(f11,axiom,(
% 0.23/0.57    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.23/0.57  fof(f36,plain,(
% 0.23/0.57    v3_ordinal1(sK0)),
% 0.23/0.57    inference(cnf_transformation,[],[f28])).
% 0.23/0.57  fof(f28,plain,(
% 0.23/0.57    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).
% 0.23/0.57  fof(f26,plain,(
% 0.23/0.57    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f27,plain,(
% 0.23/0.57    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f25,plain,(
% 0.23/0.57    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.23/0.57    inference(flattening,[],[f24])).
% 0.23/0.57  fof(f24,plain,(
% 0.23/0.57    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.23/0.57    inference(nnf_transformation,[],[f15])).
% 0.23/0.57  fof(f15,plain,(
% 0.23/0.57    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.23/0.57    inference(ennf_transformation,[],[f14])).
% 0.23/0.57  fof(f14,negated_conjecture,(
% 0.23/0.57    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.23/0.57    inference(negated_conjecture,[],[f13])).
% 0.23/0.57  fof(f13,conjecture,(
% 0.23/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.23/0.57  fof(f75,plain,(
% 0.23/0.57    ~r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | spl3_2),
% 0.23/0.57    inference(avatar_component_clause,[],[f73])).
% 0.23/0.57  fof(f73,plain,(
% 0.23/0.57    spl3_2 <=> r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.57  fof(f37,plain,(
% 0.23/0.57    v3_ordinal1(sK1)),
% 0.23/0.57    inference(cnf_transformation,[],[f28])).
% 0.23/0.57  fof(f1236,plain,(
% 0.23/0.57    ~r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~spl3_1),
% 0.23/0.57    inference(forward_demodulation,[],[f1226,f45])).
% 0.23/0.57  fof(f45,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f2])).
% 0.23/0.57  fof(f2,axiom,(
% 0.23/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.23/0.57  fof(f1226,plain,(
% 0.23/0.57    ~r2_hidden(sK1,k2_xboole_0(k2_tarski(sK0,sK0),sK0)) | ~spl3_1),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f1121,f1156,f67])).
% 0.23/0.57  fof(f67,plain,(
% 0.23/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.23/0.57    inference(equality_resolution,[],[f53])).
% 0.23/0.57  fof(f53,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.23/0.57    inference(cnf_transformation,[],[f35])).
% 0.23/0.57  fof(f35,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 0.23/0.57  fof(f34,plain,(
% 0.23/0.57    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f33,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.57    inference(rectify,[],[f32])).
% 0.23/0.57  fof(f32,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.57    inference(flattening,[],[f31])).
% 0.23/0.57  fof(f31,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.23/0.57    inference(nnf_transformation,[],[f3])).
% 0.23/0.57  fof(f3,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.23/0.57  fof(f1156,plain,(
% 0.23/0.57    ~r2_hidden(sK1,k2_tarski(sK0,sK0)) | ~spl3_1),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f1119,f52])).
% 0.23/0.57  fof(f52,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f23])).
% 0.23/0.57  fof(f23,plain,(
% 0.23/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.23/0.57    inference(ennf_transformation,[],[f12])).
% 0.23/0.57  fof(f12,axiom,(
% 0.23/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.23/0.57  fof(f1119,plain,(
% 0.23/0.57    r1_tarski(k2_tarski(sK0,sK0),sK1) | ~spl3_1),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f70,f63])).
% 0.23/0.57  fof(f63,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f51,f40])).
% 0.23/0.57  fof(f51,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f30])).
% 0.23/0.57  fof(f30,plain,(
% 0.23/0.57    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.23/0.57    inference(nnf_transformation,[],[f7])).
% 0.23/0.57  fof(f7,axiom,(
% 0.23/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.23/0.57  fof(f70,plain,(
% 0.23/0.57    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.23/0.57    inference(avatar_component_clause,[],[f69])).
% 0.23/0.57  fof(f69,plain,(
% 0.23/0.57    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.57  fof(f1121,plain,(
% 0.23/0.57    ~r2_hidden(sK1,sK0) | ~spl3_1),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f70,f47])).
% 0.23/0.57  fof(f47,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f20])).
% 0.23/0.57  fof(f20,plain,(
% 0.23/0.57    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.23/0.57    inference(ennf_transformation,[],[f1])).
% 0.23/0.57  fof(f1,axiom,(
% 0.23/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.23/0.57  fof(f1107,plain,(
% 0.23/0.57    ~spl3_2 | ~spl3_12),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f1106])).
% 0.23/0.57  fof(f1106,plain,(
% 0.23/0.57    $false | (~spl3_2 | ~spl3_12)),
% 0.23/0.57    inference(subsumption_resolution,[],[f1098,f44])).
% 0.23/0.57  fof(f44,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f5])).
% 0.23/0.57  fof(f5,axiom,(
% 0.23/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.23/0.57  fof(f1098,plain,(
% 0.23/0.57    ~r1_tarski(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) | (~spl3_2 | ~spl3_12)),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f880,f64])).
% 0.23/0.57  fof(f64,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_tarski(X0,X0),X1)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f50,f40])).
% 0.23/0.57  fof(f50,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f30])).
% 0.23/0.57  fof(f880,plain,(
% 0.23/0.57    ~r2_hidden(sK0,k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) | (~spl3_2 | ~spl3_12)),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f840,f840,f67])).
% 0.23/0.57  fof(f840,plain,(
% 0.23/0.57    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | (~spl3_2 | ~spl3_12)),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f737,f65])).
% 0.23/0.57  fof(f65,plain,(
% 0.23/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.23/0.57    inference(equality_resolution,[],[f55])).
% 0.23/0.57  fof(f55,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.23/0.57    inference(cnf_transformation,[],[f35])).
% 0.23/0.57  fof(f737,plain,(
% 0.23/0.57    ~r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | (~spl3_2 | ~spl3_12)),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f717,f52])).
% 0.23/0.57  fof(f717,plain,(
% 0.23/0.57    r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK0) | (~spl3_2 | ~spl3_12)),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f36,f78,f711,f48])).
% 0.23/0.57  fof(f48,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f29])).
% 0.23/0.57  fof(f29,plain,(
% 0.23/0.57    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.23/0.57    inference(nnf_transformation,[],[f22])).
% 0.23/0.57  fof(f22,plain,(
% 0.23/0.57    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.23/0.57    inference(flattening,[],[f21])).
% 0.23/0.57  fof(f21,plain,(
% 0.23/0.57    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.23/0.57    inference(ennf_transformation,[],[f9])).
% 0.23/0.57  fof(f9,axiom,(
% 0.23/0.57    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.23/0.57  fof(f711,plain,(
% 0.23/0.57    r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK0) | (~spl3_2 | ~spl3_12)),
% 0.23/0.57    inference(forward_demodulation,[],[f74,f277])).
% 0.23/0.57  fof(f277,plain,(
% 0.23/0.57    sK0 = sK1 | ~spl3_12),
% 0.23/0.57    inference(avatar_component_clause,[],[f275])).
% 0.23/0.57  fof(f275,plain,(
% 0.23/0.57    spl3_12 <=> sK0 = sK1),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.23/0.57  fof(f74,plain,(
% 0.23/0.57    r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | ~spl3_2),
% 0.23/0.57    inference(avatar_component_clause,[],[f73])).
% 0.23/0.57  fof(f663,plain,(
% 0.23/0.57    ~spl3_1 | spl3_11),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f662])).
% 0.23/0.57  fof(f662,plain,(
% 0.23/0.57    $false | (~spl3_1 | spl3_11)),
% 0.23/0.57    inference(subsumption_resolution,[],[f661,f642])).
% 0.23/0.57  fof(f642,plain,(
% 0.23/0.57    ~r1_ordinal1(sK0,sK1) | spl3_11),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f36,f37,f273,f48])).
% 0.23/0.57  fof(f273,plain,(
% 0.23/0.57    ~r1_tarski(sK0,sK1) | spl3_11),
% 0.23/0.57    inference(avatar_component_clause,[],[f271])).
% 0.23/0.57  fof(f271,plain,(
% 0.23/0.57    spl3_11 <=> r1_tarski(sK0,sK1)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.23/0.57  fof(f661,plain,(
% 0.23/0.57    r1_ordinal1(sK0,sK1) | ~spl3_1),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f36,f37,f650,f43])).
% 0.23/0.57  fof(f650,plain,(
% 0.23/0.57    ~r2_hidden(sK1,sK0) | ~spl3_1),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f70,f47])).
% 0.23/0.57  fof(f644,plain,(
% 0.23/0.57    ~spl3_2 | spl3_11),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f643])).
% 0.23/0.57  fof(f643,plain,(
% 0.23/0.57    $false | (~spl3_2 | spl3_11)),
% 0.23/0.57    inference(subsumption_resolution,[],[f642,f356])).
% 0.23/0.57  fof(f356,plain,(
% 0.23/0.57    r1_ordinal1(sK0,sK1) | ~spl3_2),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f36,f37,f280,f43])).
% 0.23/0.57  fof(f280,plain,(
% 0.23/0.57    ~r2_hidden(sK1,sK0) | ~spl3_2),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f164,f66])).
% 0.23/0.57  fof(f66,plain,(
% 0.23/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.23/0.57    inference(equality_resolution,[],[f54])).
% 0.23/0.57  fof(f54,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.23/0.57    inference(cnf_transformation,[],[f35])).
% 0.23/0.57  fof(f164,plain,(
% 0.23/0.57    ~r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~spl3_2),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f112,f52])).
% 0.23/0.57  fof(f112,plain,(
% 0.23/0.57    r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | ~spl3_2),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f37,f74,f78,f48])).
% 0.23/0.57  fof(f279,plain,(
% 0.23/0.57    ~spl3_11 | spl3_12 | spl3_1),
% 0.23/0.57    inference(avatar_split_clause,[],[f262,f69,f275,f271])).
% 0.23/0.57  fof(f262,plain,(
% 0.23/0.57    sK0 = sK1 | ~r1_tarski(sK0,sK1) | spl3_1),
% 0.23/0.57    inference(superposition,[],[f46,f179])).
% 0.23/0.57  fof(f179,plain,(
% 0.23/0.57    sK0 = k2_xboole_0(sK0,sK1) | spl3_1),
% 0.23/0.57    inference(superposition,[],[f136,f45])).
% 0.23/0.57  fof(f136,plain,(
% 0.23/0.57    sK0 = k2_xboole_0(sK1,sK0) | spl3_1),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f97,f46])).
% 0.23/0.57  fof(f97,plain,(
% 0.23/0.57    r1_tarski(sK1,sK0) | spl3_1),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f37,f36,f83,f48])).
% 0.23/0.57  fof(f83,plain,(
% 0.23/0.57    r1_ordinal1(sK1,sK0) | spl3_1),
% 0.23/0.57    inference(unit_resulting_resolution,[],[f37,f36,f71,f43])).
% 0.23/0.57  fof(f71,plain,(
% 0.23/0.57    ~r2_hidden(sK0,sK1) | spl3_1),
% 0.23/0.57    inference(avatar_component_clause,[],[f69])).
% 0.23/0.57  fof(f46,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f19])).
% 0.23/0.57  fof(f19,plain,(
% 0.23/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.57    inference(ennf_transformation,[],[f4])).
% 0.23/0.57  % (6934)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.57  fof(f4,axiom,(
% 0.23/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.23/0.57  fof(f77,plain,(
% 0.23/0.57    spl3_1 | spl3_2),
% 0.23/0.57    inference(avatar_split_clause,[],[f61,f73,f69])).
% 0.23/0.57  fof(f61,plain,(
% 0.23/0.57    r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | r2_hidden(sK0,sK1)),
% 0.23/0.57    inference(definition_unfolding,[],[f38,f59])).
% 0.23/0.57  fof(f38,plain,(
% 0.23/0.57    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.23/0.57    inference(cnf_transformation,[],[f28])).
% 0.23/0.57  fof(f76,plain,(
% 0.23/0.57    ~spl3_1 | ~spl3_2),
% 0.23/0.57    inference(avatar_split_clause,[],[f60,f73,f69])).
% 0.23/0.57  fof(f60,plain,(
% 0.23/0.57    ~r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 0.23/0.57    inference(definition_unfolding,[],[f39,f59])).
% 0.23/0.57  fof(f39,plain,(
% 0.23/0.57    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.23/0.57    inference(cnf_transformation,[],[f28])).
% 0.23/0.57  % SZS output end Proof for theBenchmark
% 0.23/0.57  % (6957)------------------------------
% 0.23/0.57  % (6957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (6957)Termination reason: Refutation
% 0.23/0.57  
% 0.23/0.57  % (6957)Memory used [KB]: 11257
% 0.23/0.57  % (6957)Time elapsed: 0.146 s
% 0.23/0.57  % (6957)------------------------------
% 0.23/0.57  % (6957)------------------------------
% 0.23/0.58  % (6930)Success in time 0.205 s
%------------------------------------------------------------------------------
