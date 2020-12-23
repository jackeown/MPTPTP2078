%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:28 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 226 expanded)
%              Number of leaves         :   18 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  318 (1059 expanded)
%              Number of equality atoms :   42 ( 156 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f704,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f114,f158,f182,f191,f648,f703])).

fof(f703,plain,
    ( ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(avatar_contradiction_clause,[],[f702])).

fof(f702,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f694,f649])).

fof(f649,plain,
    ( ~ r2_hidden(sK3(sK1,sK0,k1_xboole_0),k2_relat_1(sK1))
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f157,f111,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f111,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl12_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f157,plain,
    ( r2_hidden(sK3(sK1,sK0,k1_xboole_0),sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl12_4
  <=> r2_hidden(sK3(sK1,sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f694,plain,
    ( r2_hidden(sK3(sK1,sK0,k1_xboole_0),k2_relat_1(sK1))
    | ~ spl12_6 ),
    inference(unit_resulting_resolution,[],[f190,f100])).

fof(f100,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f38,f41,f40,f39])).

fof(f39,plain,(
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

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
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
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
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
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f190,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),sK3(sK1,sK0,k1_xboole_0)),sK1)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl12_6
  <=> r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),sK3(sK1,sK0,k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f648,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_contradiction_clause,[],[f647])).

fof(f647,plain,
    ( $false
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f626,f413])).

fof(f413,plain,
    ( r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl12_1
    | spl12_2 ),
    inference(forward_demodulation,[],[f401,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl12_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f401,plain,
    ( r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f52,f193,f228,f97])).

fof(f97,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f228,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),sK6(k2_relat_1(sK1),sK0)),sK1)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f192,f101])).

fof(f101,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f192,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f112,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f112,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f193,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f112,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f626,plain,
    ( ~ r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl12_1
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f57,f413,f70])).

fof(f57,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f191,plain,
    ( spl12_3
    | spl12_6
    | spl12_1 ),
    inference(avatar_split_clause,[],[f159,f106,f188,f151])).

fof(f151,plain,
    ( spl12_3
  <=> r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f159,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),sK3(sK1,sK0,k1_xboole_0)),sK1)
    | r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0)
    | spl12_1 ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | r2_hidden(k4_tarski(sK2(sK1,sK0,X0),sK3(sK1,sK0,X0)),sK1)
        | r2_hidden(sK2(sK1,sK0,X0),X0) )
    | spl12_1 ),
    inference(subsumption_resolution,[],[f118,f52])).

fof(f118,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | r2_hidden(k4_tarski(sK2(sK1,sK0,X0),sK3(sK1,sK0,X0)),sK1)
        | r2_hidden(sK2(sK1,sK0,X0),X0)
        | ~ v1_relat_1(sK1) )
    | spl12_1 ),
    inference(superposition,[],[f108,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f108,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f182,plain,(
    ~ spl12_3 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f162,f153])).

fof(f153,plain,
    ( r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f151])).

fof(f162,plain,
    ( ~ r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f57,f153,f70])).

fof(f158,plain,
    ( spl12_3
    | spl12_4
    | spl12_1 ),
    inference(avatar_split_clause,[],[f149,f106,f155,f151])).

fof(f149,plain,
    ( r2_hidden(sK3(sK1,sK0,k1_xboole_0),sK0)
    | r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0)
    | spl12_1 ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | r2_hidden(sK3(sK1,sK0,X1),sK0)
        | r2_hidden(sK2(sK1,sK0,X1),X1) )
    | spl12_1 ),
    inference(subsumption_resolution,[],[f119,f52])).

fof(f119,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | r2_hidden(sK3(sK1,sK0,X1),sK0)
        | r2_hidden(sK2(sK1,sK0,X1),X1)
        | ~ v1_relat_1(sK1) )
    | spl12_1 ),
    inference(superposition,[],[f108,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f114,plain,
    ( spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f53,f110,f106])).

fof(f53,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f113,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f54,f110,f106])).

fof(f54,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:56:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (26923)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (26915)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (26916)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (26907)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (26908)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (26905)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (26923)Refutation not found, incomplete strategy% (26923)------------------------------
% 0.21/0.51  % (26923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26923)Memory used [KB]: 10746
% 0.21/0.51  % (26923)Time elapsed: 0.060 s
% 0.21/0.51  % (26923)------------------------------
% 0.21/0.51  % (26923)------------------------------
% 0.21/0.51  % (26904)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (26924)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (26906)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (26930)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (26914)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (26921)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (26903)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (26902)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (26913)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (26922)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (26928)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (26901)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (26929)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (26926)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (26927)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (26918)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (26925)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (26919)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (26920)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (26910)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (26911)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (26912)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.52/0.56  % (26909)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.56  % (26917)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.62/0.59  % (26927)Refutation found. Thanks to Tanya!
% 1.62/0.59  % SZS status Theorem for theBenchmark
% 1.62/0.59  % SZS output start Proof for theBenchmark
% 1.62/0.62  fof(f704,plain,(
% 1.62/0.62    $false),
% 1.62/0.62    inference(avatar_sat_refutation,[],[f113,f114,f158,f182,f191,f648,f703])).
% 1.62/0.62  fof(f703,plain,(
% 1.62/0.62    ~spl12_2 | ~spl12_4 | ~spl12_6),
% 1.62/0.62    inference(avatar_contradiction_clause,[],[f702])).
% 1.62/0.62  fof(f702,plain,(
% 1.62/0.62    $false | (~spl12_2 | ~spl12_4 | ~spl12_6)),
% 1.62/0.62    inference(subsumption_resolution,[],[f694,f649])).
% 1.62/0.62  fof(f649,plain,(
% 1.62/0.62    ~r2_hidden(sK3(sK1,sK0,k1_xboole_0),k2_relat_1(sK1)) | (~spl12_2 | ~spl12_4)),
% 1.62/0.62    inference(unit_resulting_resolution,[],[f157,f111,f70])).
% 1.62/0.62  fof(f70,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f36])).
% 1.62/0.62  fof(f36,plain,(
% 1.62/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.62/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f35])).
% 1.62/0.62  fof(f35,plain,(
% 1.62/0.62    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.62/0.62    introduced(choice_axiom,[])).
% 1.62/0.62  fof(f20,plain,(
% 1.62/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.62/0.62    inference(ennf_transformation,[],[f16])).
% 1.62/0.62  fof(f16,plain,(
% 1.62/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.62/0.62    inference(rectify,[],[f2])).
% 1.62/0.62  fof(f2,axiom,(
% 1.62/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.62/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.62/0.62  fof(f111,plain,(
% 1.62/0.62    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl12_2),
% 1.62/0.62    inference(avatar_component_clause,[],[f110])).
% 1.62/0.62  fof(f110,plain,(
% 1.62/0.62    spl12_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.62/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.62/0.62  fof(f157,plain,(
% 1.62/0.62    r2_hidden(sK3(sK1,sK0,k1_xboole_0),sK0) | ~spl12_4),
% 1.62/0.62    inference(avatar_component_clause,[],[f155])).
% 1.62/0.62  fof(f155,plain,(
% 1.62/0.62    spl12_4 <=> r2_hidden(sK3(sK1,sK0,k1_xboole_0),sK0)),
% 1.62/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.62/0.62  fof(f694,plain,(
% 1.62/0.62    r2_hidden(sK3(sK1,sK0,k1_xboole_0),k2_relat_1(sK1)) | ~spl12_6),
% 1.62/0.62    inference(unit_resulting_resolution,[],[f190,f100])).
% 1.62/0.62  fof(f100,plain,(
% 1.62/0.62    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 1.62/0.62    inference(equality_resolution,[],[f72])).
% 1.62/0.62  fof(f72,plain,(
% 1.62/0.62    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.62/0.62    inference(cnf_transformation,[],[f42])).
% 1.62/0.62  fof(f42,plain,(
% 1.62/0.62    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.62/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f38,f41,f40,f39])).
% 1.62/0.62  fof(f39,plain,(
% 1.62/0.62    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 1.62/0.62    introduced(choice_axiom,[])).
% 1.62/0.62  fof(f40,plain,(
% 1.62/0.62    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0))),
% 1.62/0.62    introduced(choice_axiom,[])).
% 1.62/0.62  fof(f41,plain,(
% 1.62/0.62    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0))),
% 1.62/0.62    introduced(choice_axiom,[])).
% 1.62/0.62  fof(f38,plain,(
% 1.62/0.62    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.62/0.62    inference(rectify,[],[f37])).
% 1.62/0.62  fof(f37,plain,(
% 1.62/0.62    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.62/0.62    inference(nnf_transformation,[],[f10])).
% 1.62/0.62  fof(f10,axiom,(
% 1.62/0.62    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.62/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.62/0.62  fof(f190,plain,(
% 1.62/0.62    r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),sK3(sK1,sK0,k1_xboole_0)),sK1) | ~spl12_6),
% 1.62/0.62    inference(avatar_component_clause,[],[f188])).
% 1.62/0.62  fof(f188,plain,(
% 1.62/0.62    spl12_6 <=> r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),sK3(sK1,sK0,k1_xboole_0)),sK1)),
% 1.62/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 1.62/0.62  fof(f648,plain,(
% 1.62/0.62    ~spl12_1 | spl12_2),
% 1.62/0.62    inference(avatar_contradiction_clause,[],[f647])).
% 1.62/0.62  fof(f647,plain,(
% 1.62/0.62    $false | (~spl12_1 | spl12_2)),
% 1.62/0.62    inference(subsumption_resolution,[],[f626,f413])).
% 1.62/0.62  fof(f413,plain,(
% 1.62/0.62    r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k1_xboole_0) | (~spl12_1 | spl12_2)),
% 1.62/0.62    inference(forward_demodulation,[],[f401,f107])).
% 1.62/0.62  fof(f107,plain,(
% 1.62/0.62    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl12_1),
% 1.62/0.62    inference(avatar_component_clause,[],[f106])).
% 1.62/0.62  fof(f106,plain,(
% 1.62/0.62    spl12_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.62/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.62/0.62  fof(f401,plain,(
% 1.62/0.62    r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0)) | spl12_2),
% 1.62/0.62    inference(unit_resulting_resolution,[],[f52,f193,f228,f97])).
% 1.62/0.62  fof(f97,plain,(
% 1.62/0.62    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 1.62/0.62    inference(equality_resolution,[],[f60])).
% 1.62/0.62  fof(f60,plain,(
% 1.62/0.62    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f32])).
% 1.62/0.62  fof(f32,plain,(
% 1.62/0.62    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.62/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).
% 1.62/0.62  fof(f29,plain,(
% 1.62/0.62    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.62/0.62    introduced(choice_axiom,[])).
% 1.62/0.62  fof(f30,plain,(
% 1.62/0.62    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 1.62/0.62    introduced(choice_axiom,[])).
% 1.62/0.62  fof(f31,plain,(
% 1.62/0.62    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)))),
% 1.62/0.62    introduced(choice_axiom,[])).
% 1.62/0.62  fof(f28,plain,(
% 1.62/0.62    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.62/0.62    inference(rectify,[],[f27])).
% 1.62/0.62  fof(f27,plain,(
% 1.62/0.62    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.62/0.62    inference(nnf_transformation,[],[f18])).
% 1.62/0.62  fof(f18,plain,(
% 1.62/0.62    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.62/0.62    inference(ennf_transformation,[],[f9])).
% 1.62/0.62  fof(f9,axiom,(
% 1.62/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.62/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 1.62/0.62  fof(f228,plain,(
% 1.62/0.62    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),sK6(k2_relat_1(sK1),sK0)),sK1) | spl12_2),
% 1.62/0.62    inference(unit_resulting_resolution,[],[f192,f101])).
% 1.62/0.62  fof(f101,plain,(
% 1.62/0.62    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.62/0.62    inference(equality_resolution,[],[f71])).
% 1.62/0.62  fof(f71,plain,(
% 1.62/0.62    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.62/0.62    inference(cnf_transformation,[],[f42])).
% 1.62/0.62  fof(f192,plain,(
% 1.62/0.62    r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl12_2),
% 1.62/0.62    inference(unit_resulting_resolution,[],[f112,f68])).
% 1.62/0.62  fof(f68,plain,(
% 1.62/0.62    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f36])).
% 1.62/0.62  fof(f112,plain,(
% 1.62/0.62    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl12_2),
% 1.62/0.62    inference(avatar_component_clause,[],[f110])).
% 1.62/0.62  fof(f193,plain,(
% 1.62/0.62    r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0) | spl12_2),
% 1.62/0.62    inference(unit_resulting_resolution,[],[f112,f69])).
% 1.62/0.62  fof(f69,plain,(
% 1.62/0.62    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f36])).
% 1.62/0.62  fof(f52,plain,(
% 1.62/0.62    v1_relat_1(sK1)),
% 1.62/0.62    inference(cnf_transformation,[],[f26])).
% 1.62/0.62  fof(f26,plain,(
% 1.62/0.62    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.62/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 1.62/0.62  fof(f25,plain,(
% 1.62/0.62    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.62/0.62    introduced(choice_axiom,[])).
% 1.62/0.62  fof(f24,plain,(
% 1.62/0.62    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.62/0.62    inference(flattening,[],[f23])).
% 1.62/0.62  fof(f23,plain,(
% 1.62/0.62    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.62/0.62    inference(nnf_transformation,[],[f17])).
% 1.62/0.62  fof(f17,plain,(
% 1.62/0.62    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.62/0.62    inference(ennf_transformation,[],[f14])).
% 1.62/0.62  fof(f14,negated_conjecture,(
% 1.62/0.62    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.62/0.62    inference(negated_conjecture,[],[f13])).
% 1.62/0.62  fof(f13,conjecture,(
% 1.62/0.62    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.62/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 1.62/0.62  fof(f626,plain,(
% 1.62/0.62    ~r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k1_xboole_0) | (~spl12_1 | spl12_2)),
% 1.62/0.62    inference(unit_resulting_resolution,[],[f57,f413,f70])).
% 1.62/0.62  fof(f57,plain,(
% 1.62/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f4])).
% 1.62/0.62  fof(f4,axiom,(
% 1.62/0.62    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.62/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.62/0.62  fof(f191,plain,(
% 1.62/0.62    spl12_3 | spl12_6 | spl12_1),
% 1.62/0.62    inference(avatar_split_clause,[],[f159,f106,f188,f151])).
% 1.62/0.62  fof(f151,plain,(
% 1.62/0.62    spl12_3 <=> r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0)),
% 1.62/0.62    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.62/0.62  fof(f159,plain,(
% 1.62/0.62    r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),sK3(sK1,sK0,k1_xboole_0)),sK1) | r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0) | spl12_1),
% 1.62/0.62    inference(equality_resolution,[],[f121])).
% 1.62/0.62  fof(f121,plain,(
% 1.62/0.62    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(k4_tarski(sK2(sK1,sK0,X0),sK3(sK1,sK0,X0)),sK1) | r2_hidden(sK2(sK1,sK0,X0),X0)) ) | spl12_1),
% 1.62/0.62    inference(subsumption_resolution,[],[f118,f52])).
% 1.62/0.62  fof(f118,plain,(
% 1.62/0.62    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(k4_tarski(sK2(sK1,sK0,X0),sK3(sK1,sK0,X0)),sK1) | r2_hidden(sK2(sK1,sK0,X0),X0) | ~v1_relat_1(sK1)) ) | spl12_1),
% 1.62/0.62    inference(superposition,[],[f108,f61])).
% 1.62/0.62  fof(f61,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(sK2(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f32])).
% 1.62/0.62  fof(f108,plain,(
% 1.62/0.62    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl12_1),
% 1.62/0.62    inference(avatar_component_clause,[],[f106])).
% 1.62/0.62  fof(f182,plain,(
% 1.62/0.62    ~spl12_3),
% 1.62/0.62    inference(avatar_contradiction_clause,[],[f181])).
% 1.62/0.62  fof(f181,plain,(
% 1.62/0.62    $false | ~spl12_3),
% 1.62/0.62    inference(subsumption_resolution,[],[f162,f153])).
% 1.62/0.62  fof(f153,plain,(
% 1.62/0.62    r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0) | ~spl12_3),
% 1.62/0.62    inference(avatar_component_clause,[],[f151])).
% 1.62/0.62  fof(f162,plain,(
% 1.62/0.62    ~r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0) | ~spl12_3),
% 1.62/0.62    inference(unit_resulting_resolution,[],[f57,f153,f70])).
% 1.62/0.62  fof(f158,plain,(
% 1.62/0.62    spl12_3 | spl12_4 | spl12_1),
% 1.62/0.62    inference(avatar_split_clause,[],[f149,f106,f155,f151])).
% 1.62/0.62  fof(f149,plain,(
% 1.62/0.62    r2_hidden(sK3(sK1,sK0,k1_xboole_0),sK0) | r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_xboole_0) | spl12_1),
% 1.62/0.62    inference(equality_resolution,[],[f122])).
% 1.62/0.62  fof(f122,plain,(
% 1.62/0.62    ( ! [X1] : (k1_xboole_0 != X1 | r2_hidden(sK3(sK1,sK0,X1),sK0) | r2_hidden(sK2(sK1,sK0,X1),X1)) ) | spl12_1),
% 1.62/0.62    inference(subsumption_resolution,[],[f119,f52])).
% 1.62/0.62  fof(f119,plain,(
% 1.62/0.62    ( ! [X1] : (k1_xboole_0 != X1 | r2_hidden(sK3(sK1,sK0,X1),sK0) | r2_hidden(sK2(sK1,sK0,X1),X1) | ~v1_relat_1(sK1)) ) | spl12_1),
% 1.62/0.62    inference(superposition,[],[f108,f62])).
% 1.62/0.62  fof(f62,plain,(
% 1.62/0.62    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 1.62/0.62    inference(cnf_transformation,[],[f32])).
% 1.62/0.62  fof(f114,plain,(
% 1.62/0.62    spl12_1 | spl12_2),
% 1.62/0.62    inference(avatar_split_clause,[],[f53,f110,f106])).
% 1.62/0.62  fof(f53,plain,(
% 1.62/0.62    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.62/0.62    inference(cnf_transformation,[],[f26])).
% 1.62/0.62  fof(f113,plain,(
% 1.62/0.62    ~spl12_1 | ~spl12_2),
% 1.62/0.62    inference(avatar_split_clause,[],[f54,f110,f106])).
% 1.62/0.62  fof(f54,plain,(
% 1.62/0.62    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.62/0.62    inference(cnf_transformation,[],[f26])).
% 1.62/0.62  % SZS output end Proof for theBenchmark
% 1.62/0.62  % (26927)------------------------------
% 1.62/0.62  % (26927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.62  % (26927)Termination reason: Refutation
% 1.62/0.62  
% 1.62/0.62  % (26927)Memory used [KB]: 11385
% 1.62/0.62  % (26927)Time elapsed: 0.176 s
% 1.62/0.62  % (26927)------------------------------
% 1.62/0.62  % (26927)------------------------------
% 1.62/0.62  % (26900)Success in time 0.261 s
%------------------------------------------------------------------------------
