%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 166 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 ( 357 expanded)
%              Number of equality atoms :   40 (  98 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f77,f88,f107,f114,f160,f167])).

fof(f167,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f163,f29])).

fof(f29,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f163,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0)),k1_xboole_0)
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f106,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f106,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_8
  <=> r2_hidden(sK1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f160,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f156,f29])).

fof(f156,plain,
    ( ~ r1_xboole_0(k3_enumset1(k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0))),k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0))),k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0))),k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0))),k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0)))),k1_xboole_0)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f120,f45])).

fof(f120,plain,
    ( r2_hidden(k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f55,f102,f89])).

fof(f89,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_xboole_0,X0),X0)
        | r2_hidden(k4_tarski(sK2(k1_xboole_0,X0),sK3(k1_xboole_0,X0)),k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl5_1 ),
    inference(superposition,[],[f50,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
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
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
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
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f50,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f102,plain,
    ( ! [X6] : ~ r2_hidden(X6,k2_relat_1(k1_xboole_0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_7
  <=> ! [X6] : ~ r2_hidden(X6,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f55,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f114,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f110,f29])).

fof(f110,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)),k1_xboole_0)
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f108,f45])).

fof(f108,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f99,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f99,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f107,plain,
    ( ~ spl5_6
    | spl5_7
    | spl5_8
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f95,f49,f104,f101,f97])).

fof(f95,plain,
    ( ! [X6] :
        ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X6,k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f34,f50])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f20])).

fof(f20,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK1(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f88,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f84,f29])).

fof(f84,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f62,f45])).

fof(f62,plain,
    ( r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_3
  <=> r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f77,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f73,f29])).

fof(f73,plain,
    ( ~ r1_xboole_0(k3_enumset1(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0))),k1_xboole_0)
    | spl5_1
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f69,f45])).

fof(f69,plain,
    ( r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f68,f63])).

fof(f63,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f68,plain,
    ( r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl5_1 ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | r2_hidden(k4_tarski(sK2(k1_xboole_0,X0),sK3(k1_xboole_0,X0)),k1_xboole_0)
        | r2_hidden(sK2(k1_xboole_0,X0),X0) )
    | spl5_1 ),
    inference(superposition,[],[f51,f37])).

fof(f51,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f56,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f28,f53,f49])).

fof(f28,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (14615)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (14615)Refutation not found, incomplete strategy% (14615)------------------------------
% 0.21/0.50  % (14615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14639)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (14615)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14615)Memory used [KB]: 10618
% 0.21/0.51  % (14615)Time elapsed: 0.105 s
% 0.21/0.51  % (14615)------------------------------
% 0.21/0.51  % (14615)------------------------------
% 0.21/0.51  % (14616)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (14617)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (14614)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (14618)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (14623)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (14623)Refutation not found, incomplete strategy% (14623)------------------------------
% 0.21/0.51  % (14623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14631)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (14623)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14623)Memory used [KB]: 10618
% 0.21/0.52  % (14623)Time elapsed: 0.119 s
% 0.21/0.52  % (14623)------------------------------
% 0.21/0.52  % (14623)------------------------------
% 0.21/0.52  % (14621)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (14635)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (14635)Refutation not found, incomplete strategy% (14635)------------------------------
% 0.21/0.52  % (14635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14635)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14635)Memory used [KB]: 10618
% 0.21/0.52  % (14635)Time elapsed: 0.085 s
% 0.21/0.52  % (14635)------------------------------
% 0.21/0.52  % (14635)------------------------------
% 0.21/0.52  % (14632)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (14639)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f56,f77,f88,f107,f114,f160,f167])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ~spl5_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    $false | ~spl5_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f163,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ~r1_xboole_0(k3_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0)),k1_xboole_0) | ~spl5_8),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f106,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f39,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f40,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | ~spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl5_8 <=> r2_hidden(sK1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ~spl5_1 | spl5_2 | ~spl5_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    $false | (~spl5_1 | spl5_2 | ~spl5_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f156,f29])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ~r1_xboole_0(k3_enumset1(k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0))),k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0))),k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0))),k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0))),k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0)))),k1_xboole_0) | (~spl5_1 | spl5_2 | ~spl5_7)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f120,f45])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(k1_xboole_0,k2_relat_1(k1_xboole_0)),sK3(k1_xboole_0,k2_relat_1(k1_xboole_0))),k1_xboole_0) | (~spl5_1 | spl5_2 | ~spl5_7)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f55,f102,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,X0),X0) | r2_hidden(k4_tarski(sK2(k1_xboole_0,X0),sK3(k1_xboole_0,X0)),k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl5_1),
% 0.21/0.52    inference(superposition,[],[f50,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl5_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X6] : (~r2_hidden(X6,k2_relat_1(k1_xboole_0))) ) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl5_7 <=> ! [X6] : ~r2_hidden(X6,k2_relat_1(k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl5_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl5_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    $false | spl5_6),
% 0.21/0.52    inference(subsumption_resolution,[],[f110,f29])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ~r1_xboole_0(k3_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0),sK0(k1_xboole_0)),k1_xboole_0) | spl5_6),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f108,f45])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    r2_hidden(sK0(k1_xboole_0),k1_xboole_0) | spl5_6),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f99,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~v1_relat_1(k1_xboole_0) | spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl5_6 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ~spl5_6 | spl5_7 | spl5_8 | ~spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f95,f49,f104,f101,f97])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X6] : (r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | ~r2_hidden(X6,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl5_1),
% 0.21/0.52    inference(superposition,[],[f34,f50])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK1(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(sK1(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK1(X1),k1_relat_1(X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ~spl5_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    $false | ~spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f84,f29])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~r1_xboole_0(k3_enumset1(sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl5_3),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f62,f45])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl5_3 <=> r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl5_1 | spl5_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    $false | (spl5_1 | spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f73,f29])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ~r1_xboole_0(k3_enumset1(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0))),k1_xboole_0) | (spl5_1 | spl5_3)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f69,f45])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (spl5_1 | spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ~r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl5_1),
% 0.21/0.52    inference(equality_resolution,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(k4_tarski(sK2(k1_xboole_0,X0),sK3(k1_xboole_0,X0)),k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,X0),X0)) ) | spl5_1),
% 0.21/0.52    inference(superposition,[],[f51,f37])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f49])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f53,f49])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14639)------------------------------
% 0.21/0.53  % (14639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14639)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14639)Memory used [KB]: 10746
% 0.21/0.53  % (14639)Time elapsed: 0.132 s
% 0.21/0.53  % (14639)------------------------------
% 0.21/0.53  % (14639)------------------------------
% 0.21/0.53  % (14627)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (14611)Success in time 0.167 s
%------------------------------------------------------------------------------
