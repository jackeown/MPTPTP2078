%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 155 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  258 ( 550 expanded)
%              Number of equality atoms :   42 ( 113 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f157,f182,f324,f328,f370])).

fof(f370,plain,
    ( spl12_1
    | ~ spl12_4 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f365,f96])).

fof(f96,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl12_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f365,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl12_4 ),
    inference(resolution,[],[f342,f61])).

fof(f61,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f342,plain,
    ( r2_hidden(k4_tarski(sK0,k4_tarski(sK2(k11_relat_1(sK1,sK0)),sK3(k11_relat_1(sK1,sK0)))),sK1)
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f338,f41])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f338,plain,
    ( r2_hidden(k4_tarski(sK0,k4_tarski(sK2(k11_relat_1(sK1,sK0)),sK3(k11_relat_1(sK1,sK0)))),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl12_4 ),
    inference(resolution,[],[f156,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f156,plain,
    ( r2_hidden(k4_tarski(sK2(k11_relat_1(sK1,sK0)),sK3(k11_relat_1(sK1,sK0))),k11_relat_1(sK1,sK0))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl12_4
  <=> r2_hidden(k4_tarski(sK2(k11_relat_1(sK1,sK0)),sK3(k11_relat_1(sK1,sK0))),k11_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f328,plain,
    ( spl12_1
    | ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f325,f96])).

fof(f325,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f65,f100])).

fof(f100,plain,
    ( sQ11_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl12_2
  <=> sQ11_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f65,plain,
    ( ~ sQ11_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(equality_proxy_replacement,[],[f42,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( sQ11_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).

fof(f42,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f324,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f100,f44,f90,f218,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ sQ11_eqProxy(X2,X3)
      | ~ sQ11_eqProxy(X0,X1)
      | r1_xboole_0(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f63])).

fof(f218,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK9(sK1,sK0),X0),k11_relat_1(sK1,sK0))
    | ~ spl12_1 ),
    inference(resolution,[],[f191,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f191,plain,
    ( r2_hidden(sK9(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f187,f41])).

fof(f187,plain,
    ( r2_hidden(sK9(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl12_1 ),
    inference(resolution,[],[f184,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f184,plain,
    ( r2_hidden(k4_tarski(sK0,sK9(sK1,sK0)),sK1)
    | ~ spl12_1 ),
    inference(resolution,[],[f95,f62])).

fof(f62,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f90,plain,(
    ! [X0] : sQ11_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f63])).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f182,plain,
    ( spl12_1
    | spl12_3 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl12_1
    | spl12_3 ),
    inference(subsumption_resolution,[],[f177,f96])).

fof(f177,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | spl12_3 ),
    inference(resolution,[],[f174,f61])).

fof(f174,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(k11_relat_1(sK1,sK0))),sK1)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f171,f41])).

fof(f171,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(k11_relat_1(sK1,sK0))),sK1)
    | ~ v1_relat_1(sK1)
    | spl12_3 ),
    inference(resolution,[],[f160,f59])).

fof(f160,plain,
    ( r2_hidden(sK4(k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))
    | spl12_3 ),
    inference(resolution,[],[f152,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK4(X0)
          & r2_hidden(sK4(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK5(X4),sK6(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK4(X0)
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK5(X4),sK6(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f152,plain,
    ( ~ v1_relat_1(k11_relat_1(sK1,sK0))
    | spl12_3 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl12_3
  <=> v1_relat_1(k11_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f157,plain,
    ( ~ spl12_3
    | spl12_4
    | spl12_2 ),
    inference(avatar_split_clause,[],[f115,f98,f154,f150])).

fof(f115,plain,
    ( r2_hidden(k4_tarski(sK2(k11_relat_1(sK1,sK0)),sK3(k11_relat_1(sK1,sK0))),k11_relat_1(sK1,sK0))
    | ~ v1_relat_1(k11_relat_1(sK1,sK0))
    | spl12_2 ),
    inference(resolution,[],[f67,f99])).

fof(f99,plain,
    ( ~ sQ11_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | spl12_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f67,plain,(
    ! [X0] :
      ( sQ11_eqProxy(k1_xboole_0,X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f46,f63])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f101,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f64,f98,f94])).

fof(f64,plain,
    ( sQ11_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(equality_proxy_replacement,[],[f43,f63])).

fof(f43,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (17182)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.44  % (17183)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (17175)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (17175)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (17191)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (17184)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (17191)Refutation not found, incomplete strategy% (17191)------------------------------
% 0.20/0.48  % (17191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17191)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (17191)Memory used [KB]: 10618
% 0.20/0.48  % (17191)Time elapsed: 0.069 s
% 0.20/0.48  % (17191)------------------------------
% 0.20/0.48  % (17191)------------------------------
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f372,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f101,f157,f182,f324,f328,f370])).
% 0.20/0.48  fof(f370,plain,(
% 0.20/0.48    spl12_1 | ~spl12_4),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f369])).
% 0.20/0.48  fof(f369,plain,(
% 0.20/0.48    $false | (spl12_1 | ~spl12_4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f365,f96])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl12_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    spl12_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.20/0.48  fof(f365,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl12_4),
% 0.20/0.48    inference(resolution,[],[f342,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f31,f34,f33,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.48    inference(rectify,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.48  fof(f342,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,k4_tarski(sK2(k11_relat_1(sK1,sK0)),sK3(k11_relat_1(sK1,sK0)))),sK1) | ~spl12_4),
% 0.20/0.48    inference(subsumption_resolution,[],[f338,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.48    inference(negated_conjecture,[],[f9])).
% 0.20/0.48  fof(f9,conjecture,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.48  fof(f338,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,k4_tarski(sK2(k11_relat_1(sK1,sK0)),sK3(k11_relat_1(sK1,sK0)))),sK1) | ~v1_relat_1(sK1) | ~spl12_4),
% 0.20/0.48    inference(resolution,[],[f156,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK2(k11_relat_1(sK1,sK0)),sK3(k11_relat_1(sK1,sK0))),k11_relat_1(sK1,sK0)) | ~spl12_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f154])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    spl12_4 <=> r2_hidden(k4_tarski(sK2(k11_relat_1(sK1,sK0)),sK3(k11_relat_1(sK1,sK0))),k11_relat_1(sK1,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.20/0.48  fof(f328,plain,(
% 0.20/0.48    spl12_1 | ~spl12_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f327])).
% 0.20/0.48  fof(f327,plain,(
% 0.20/0.48    $false | (spl12_1 | ~spl12_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f325,f96])).
% 0.20/0.48  fof(f325,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl12_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f65,f100])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    sQ11_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | ~spl12_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f98])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl12_2 <=> sQ11_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ~sQ11_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.48    inference(equality_proxy_replacement,[],[f42,f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ! [X1,X0] : (sQ11_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f324,plain,(
% 0.20/0.48    ~spl12_1 | ~spl12_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f323])).
% 0.20/0.48  fof(f323,plain,(
% 0.20/0.48    $false | (~spl12_1 | ~spl12_2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f100,f44,f90,f218,f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X2) | ~sQ11_eqProxy(X2,X3) | ~sQ11_eqProxy(X0,X1) | r1_xboole_0(X1,X3)) )),
% 0.20/0.48    inference(equality_proxy_axiom,[],[f63])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK9(sK1,sK0),X0),k11_relat_1(sK1,sK0))) ) | ~spl12_1),
% 0.20/0.48    inference(resolution,[],[f191,f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    r2_hidden(sK9(sK1,sK0),k11_relat_1(sK1,sK0)) | ~spl12_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f187,f41])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    r2_hidden(sK9(sK1,sK0),k11_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl12_1),
% 0.20/0.48    inference(resolution,[],[f184,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,sK9(sK1,sK0)),sK1) | ~spl12_1),
% 0.20/0.48    inference(resolution,[],[f95,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl12_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f94])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ( ! [X0] : (sQ11_eqProxy(X0,X0)) )),
% 0.20/0.48    inference(equality_proxy_axiom,[],[f63])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    spl12_1 | spl12_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f181])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    $false | (spl12_1 | spl12_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f177,f96])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(sK1)) | spl12_3),
% 0.20/0.48    inference(resolution,[],[f174,f61])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,sK4(k11_relat_1(sK1,sK0))),sK1) | spl12_3),
% 0.20/0.48    inference(subsumption_resolution,[],[f171,f41])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK0,sK4(k11_relat_1(sK1,sK0))),sK1) | ~v1_relat_1(sK1) | spl12_3),
% 0.20/0.48    inference(resolution,[],[f160,f59])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    r2_hidden(sK4(k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) | spl12_3),
% 0.20/0.48    inference(resolution,[],[f152,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK4(X0),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK4(X0) & r2_hidden(sK4(X0),X0))) & (! [X4] : (k4_tarski(sK5(X4),sK6(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f28,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK4(X0) & r2_hidden(sK4(X0),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK5(X4),sK6(X4)) = X4)),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(rectify,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    ~v1_relat_1(k11_relat_1(sK1,sK0)) | spl12_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f150])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    spl12_3 <=> v1_relat_1(k11_relat_1(sK1,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    ~spl12_3 | spl12_4 | spl12_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f115,f98,f154,f150])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK2(k11_relat_1(sK1,sK0)),sK3(k11_relat_1(sK1,sK0))),k11_relat_1(sK1,sK0)) | ~v1_relat_1(k11_relat_1(sK1,sK0)) | spl12_2),
% 0.20/0.48    inference(resolution,[],[f67,f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ~sQ11_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | spl12_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f98])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X0] : (sQ11_eqProxy(k1_xboole_0,X0) | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(equality_proxy_replacement,[],[f46,f63])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ~spl12_1 | spl12_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f64,f98,f94])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    sQ11_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.48    inference(equality_proxy_replacement,[],[f43,f63])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17175)------------------------------
% 0.20/0.48  % (17175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17175)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17175)Memory used [KB]: 6268
% 0.20/0.48  % (17175)Time elapsed: 0.069 s
% 0.20/0.48  % (17175)------------------------------
% 0.20/0.48  % (17175)------------------------------
% 0.20/0.48  % (17166)Success in time 0.129 s
%------------------------------------------------------------------------------
