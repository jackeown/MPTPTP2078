%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 123 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  243 ( 432 expanded)
%              Number of equality atoms :   34 (  86 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f114,f117,f261])).

fof(f261,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f65,f250,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sQ7_eqProxy(X1,X0)
      | ~ sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f250,plain,
    ( ! [X2] : ~ sQ7_eqProxy(sK6(sK1,sK0),X2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f248,f70])).

fof(f70,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f248,plain,
    ( ! [X2] :
        ( ~ sQ7_eqProxy(sK6(sK1,sK0),X2)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f245,f46])).

fof(f46,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),sK1)
        | ~ sQ7_eqProxy(X0,X1) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f239,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
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

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f239,plain,
    ( ! [X0,X1] :
        ( ~ sQ7_eqProxy(X0,X1)
        | ~ r2_hidden(k4_tarski(sK0,X0),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl8_2 ),
    inference(resolution,[],[f237,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f237,plain,
    ( ! [X28,X29] :
        ( ~ r2_hidden(X28,k11_relat_1(sK1,sK0))
        | ~ sQ7_eqProxy(X28,X29) )
    | ~ spl8_2 ),
    inference(resolution,[],[f220,f75])).

fof(f75,plain,
    ( sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl8_2
  <=> sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f220,plain,(
    ! [X10,X8,X9] :
      ( ~ sQ7_eqProxy(k1_xboole_0,X9)
      | ~ sQ7_eqProxy(X8,X10)
      | ~ r2_hidden(X8,X9) ) ),
    inference(resolution,[],[f206,f66])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ7_eqProxy(X0,k1_xboole_0)
      | ~ r2_hidden(X1,X0)
      | ~ sQ7_eqProxy(X1,X2) ) ),
    inference(resolution,[],[f63,f82])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f37,f44])).

fof(f44,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ r2_hidden(X0,X2)
      | ~ sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f47])).

fof(f65,plain,(
    ! [X0] : sQ7_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f47])).

fof(f117,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f115,f75])).

fof(f115,plain,
    ( ~ sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f49,f71])).

fof(f71,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f49,plain,
    ( ~ sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(equality_proxy_replacement,[],[f30,f47])).

fof(f30,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f114,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f105,f74])).

fof(f74,plain,
    ( ~ sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f105,plain,
    ( sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | spl8_1 ),
    inference(resolution,[],[f99,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | sQ7_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f34,f47])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f99,plain,
    ( ! [X0] : ~ r2_hidden(X0,k11_relat_1(sK1,sK0))
    | spl8_1 ),
    inference(resolution,[],[f98,f71])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k11_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f96,f45])).

fof(f45,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK1)
      | ~ r2_hidden(X0,k11_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f43,f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f48,f73,f69])).

fof(f48,plain,
    ( sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(equality_proxy_replacement,[],[f31,f47])).

fof(f31,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (27987)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (27987)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f262,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f76,f114,f117,f261])).
% 0.20/0.47  fof(f261,plain,(
% 0.20/0.47    ~spl8_1 | ~spl8_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f254])).
% 0.20/0.47  fof(f254,plain,(
% 0.20/0.47    $false | (~spl8_1 | ~spl8_2)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f65,f250,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sQ7_eqProxy(X1,X0) | ~sQ7_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    ( ! [X2] : (~sQ7_eqProxy(sK6(sK1,sK0),X2)) ) | (~spl8_1 | ~spl8_2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f248,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl8_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl8_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.47  fof(f248,plain,(
% 0.20/0.47    ( ! [X2] : (~sQ7_eqProxy(sK6(sK1,sK0),X2) | ~r2_hidden(sK0,k1_relat_1(sK1))) ) | ~spl8_2),
% 0.20/0.47    inference(resolution,[],[f245,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.47    inference(equality_resolution,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f23,f26,f25,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.47    inference(rectify,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.47  fof(f245,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK0,X0),sK1) | ~sQ7_eqProxy(X0,X1)) ) | ~spl8_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f239,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.47  fof(f6,conjecture,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~sQ7_eqProxy(X0,X1) | ~r2_hidden(k4_tarski(sK0,X0),sK1) | ~v1_relat_1(sK1)) ) | ~spl8_2),
% 0.20/0.47    inference(resolution,[],[f237,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(nnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    ( ! [X28,X29] : (~r2_hidden(X28,k11_relat_1(sK1,sK0)) | ~sQ7_eqProxy(X28,X29)) ) | ~spl8_2),
% 0.20/0.47    inference(resolution,[],[f220,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | ~spl8_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl8_2 <=> sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    ( ! [X10,X8,X9] : (~sQ7_eqProxy(k1_xboole_0,X9) | ~sQ7_eqProxy(X8,X10) | ~r2_hidden(X8,X9)) )),
% 0.20/0.47    inference(resolution,[],[f206,f66])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~sQ7_eqProxy(X0,k1_xboole_0) | ~r2_hidden(X1,X0) | ~sQ7_eqProxy(X1,X2)) )),
% 0.20/0.47    inference(resolution,[],[f63,f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(resolution,[],[f37,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    inference(equality_resolution,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(rectify,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~sQ7_eqProxy(X2,X3) | ~r2_hidden(X0,X2) | ~sQ7_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f47])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (sQ7_eqProxy(X0,X0)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f47])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl8_1 | ~spl8_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    $false | (spl8_1 | ~spl8_2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f115,f75])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    ~sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | spl8_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f49,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl8_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f69])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ~sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f30,f47])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl8_1 | spl8_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    $false | (spl8_1 | spl8_2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f105,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ~sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | spl8_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f73])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | spl8_1),
% 0.20/0.47    inference(resolution,[],[f99,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2(X0),X0) | sQ7_eqProxy(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f34,f47])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k11_relat_1(sK1,sK0))) ) | spl8_1),
% 0.20/0.47    inference(resolution,[],[f98,f71])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X0,k11_relat_1(sK1,X1))) )),
% 0.20/0.47    inference(resolution,[],[f96,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.47    inference(equality_resolution,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK1) | ~r2_hidden(X0,k11_relat_1(sK1,X1))) )),
% 0.20/0.47    inference(resolution,[],[f43,f29])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ~spl8_1 | spl8_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f73,f69])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    sQ7_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f31,f47])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (27987)------------------------------
% 0.20/0.47  % (27987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (27987)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (27987)Memory used [KB]: 6268
% 0.20/0.47  % (27987)Time elapsed: 0.021 s
% 0.20/0.47  % (27987)------------------------------
% 0.20/0.47  % (27987)------------------------------
% 0.20/0.47  % (27981)Success in time 0.117 s
%------------------------------------------------------------------------------
