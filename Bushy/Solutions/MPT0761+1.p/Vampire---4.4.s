%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t5_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:15 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 192 expanded)
%              Number of leaves         :   13 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  295 ( 607 expanded)
%              Number of equality atoms :   19 (  46 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f85,f96,f100,f128,f140,f167,f178,f200,f259])).

fof(f259,plain,
    ( ~ spl6_0
    | spl6_5
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f257,f104])).

fof(f104,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_5
  <=> ~ r1_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f257,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f256,f73])).

fof(f73,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f256,plain,
    ( ~ v1_relat_1(sK0)
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f254,f127])).

fof(f127,plain,
    ( r2_hidden(sK4(sK0,sK1(sK0,k3_relat_1(sK0))),sK1(sK0,k3_relat_1(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_10
  <=> r2_hidden(sK4(sK0,sK1(sK0,k3_relat_1(sK0))),sK1(sK0,k3_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f254,plain,
    ( ~ r2_hidden(sK4(sK0,sK1(sK0,k3_relat_1(sK0))),sK1(sK0,k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl6_12 ),
    inference(resolution,[],[f139,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_xboole_0(k1_wellord1(X0,X3),sK1(X0,X1))
      | ~ r2_hidden(X3,sK1(X0,X1))
      | ~ v1_relat_1(X0)
      | r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_wellord1(X0,X1)
        <=> ! [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(k1_wellord1(X0,X3),X2)
                  & r2_hidden(X3,X2) )
              | k1_xboole_0 = X2
              | ~ r1_tarski(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_wellord1(X0,X1)
        <=> ! [X2] :
              ~ ( ! [X3] :
                    ~ ( r1_xboole_0(k1_wellord1(X0,X3),X2)
                      & r2_hidden(X3,X2) )
                & k1_xboole_0 != X2
                & r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t5_wellord1.p',d3_wellord1)).

fof(f139,plain,
    ( r1_xboole_0(k1_wellord1(sK0,sK4(sK0,sK1(sK0,k3_relat_1(sK0)))),sK1(sK0,k3_relat_1(sK0)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_12
  <=> r1_xboole_0(k1_wellord1(sK0,sK4(sK0,sK1(sK0,k3_relat_1(sK0)))),sK1(sK0,k3_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f200,plain,
    ( ~ spl6_5
    | ~ spl6_0
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f195,f176,f165,f72,f103])).

fof(f165,plain,
    ( spl6_18
  <=> r2_hidden(sK2(sK0,sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f176,plain,
    ( spl6_20
  <=> r1_xboole_0(k1_wellord1(sK0,sK2(sK0,sK3(sK0))),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f195,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f44,f186])).

fof(f186,plain,
    ( v1_wellord1(sK0)
    | ~ spl6_0
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f185,f73])).

fof(f185,plain,
    ( ~ v1_relat_1(sK0)
    | v1_wellord1(sK0)
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f183,f166])).

fof(f166,plain,
    ( r2_hidden(sK2(sK0,sK3(sK0)),sK3(sK0))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f183,plain,
    ( ~ r2_hidden(sK2(sK0,sK3(sK0)),sK3(sK0))
    | ~ v1_relat_1(sK0)
    | v1_wellord1(sK0)
    | ~ spl6_20 ),
    inference(resolution,[],[f177,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK3(X0))
      | ~ r2_hidden(X2,sK3(X0))
      | ~ v1_relat_1(X0)
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                & r2_hidden(X2,X1) )
            | k1_xboole_0 = X1
            | ~ r1_tarski(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> ! [X1] :
            ~ ( ! [X2] :
                  ~ ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t5_wellord1.p',d2_wellord1)).

fof(f177,plain,
    ( r1_xboole_0(k1_wellord1(sK0,sK2(sK0,sK3(sK0))),sK3(sK0))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f176])).

fof(f44,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_wellord1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ( v1_wellord1(X0)
      <~> r1_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v1_wellord1(X0)
        <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t5_wellord1.p',t5_wellord1)).

fof(f178,plain,
    ( spl6_20
    | ~ spl6_0
    | ~ spl6_4
    | spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f169,f98,f94,f83,f72,f176])).

fof(f83,plain,
    ( spl6_4
  <=> r1_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f94,plain,
    ( spl6_7
  <=> k1_xboole_0 != sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f98,plain,
    ( spl6_8
  <=> r1_tarski(sK3(sK0),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f169,plain,
    ( r1_xboole_0(k1_wellord1(sK0,sK2(sK0,sK3(sK0))),sK3(sK0))
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f168,f73])).

fof(f168,plain,
    ( r1_xboole_0(k1_wellord1(sK0,sK2(sK0,sK3(sK0))),sK3(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(resolution,[],[f150,f84])).

fof(f84,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f150,plain,
    ( ! [X1] :
        ( ~ r1_wellord1(X1,k3_relat_1(sK0))
        | r1_xboole_0(k1_wellord1(X1,sK2(X1,sK3(sK0))),sK3(sK0))
        | ~ v1_relat_1(X1) )
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f148,f95])).

fof(f95,plain,
    ( k1_xboole_0 != sK3(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f148,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = sK3(sK0)
        | r1_xboole_0(k1_wellord1(X1,sK2(X1,sK3(sK0))),sK3(sK0))
        | ~ r1_wellord1(X1,k3_relat_1(sK0)) )
    | ~ spl6_8 ),
    inference(resolution,[],[f99,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X2
      | r1_xboole_0(k1_wellord1(X0,sK2(X0,X2)),X2)
      | ~ r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f99,plain,
    ( r1_tarski(sK3(sK0),k3_relat_1(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f167,plain,
    ( spl6_18
    | ~ spl6_0
    | ~ spl6_4
    | spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f163,f98,f94,f83,f72,f165])).

fof(f163,plain,
    ( r2_hidden(sK2(sK0,sK3(sK0)),sK3(sK0))
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f162,f73])).

fof(f162,plain,
    ( r2_hidden(sK2(sK0,sK3(sK0)),sK3(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(resolution,[],[f149,f84])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r1_wellord1(X0,k3_relat_1(sK0))
        | r2_hidden(sK2(X0,sK3(sK0)),sK3(sK0))
        | ~ v1_relat_1(X0) )
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f147,f95])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = sK3(sK0)
        | r2_hidden(sK2(X0,sK3(sK0)),sK3(sK0))
        | ~ r1_wellord1(X0,k3_relat_1(sK0)) )
    | ~ spl6_8 ),
    inference(resolution,[],[f99,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X2
      | r2_hidden(sK2(X0,X2),X2)
      | ~ r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f140,plain,
    ( spl6_12
    | ~ spl6_0
    | ~ spl6_2
    | spl6_5 ),
    inference(avatar_split_clause,[],[f131,f103,f80,f72,f138])).

fof(f80,plain,
    ( spl6_2
  <=> v1_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f131,plain,
    ( r1_xboole_0(k1_wellord1(sK0,sK4(sK0,sK1(sK0,k3_relat_1(sK0)))),sK1(sK0,k3_relat_1(sK0)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f130,f104])).

fof(f130,plain,
    ( r1_xboole_0(k1_wellord1(sK0,sK4(sK0,sK1(sK0,k3_relat_1(sK0)))),sK1(sK0,k3_relat_1(sK0)))
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f129,f73])).

fof(f129,plain,
    ( ~ v1_relat_1(sK0)
    | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,sK1(sK0,k3_relat_1(sK0)))),sK1(sK0,k3_relat_1(sK0)))
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f114,f81])).

fof(f81,plain,
    ( v1_wellord1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f114,plain,
    ( ! [X6] :
        ( ~ v1_wellord1(X6)
        | ~ v1_relat_1(X6)
        | r1_xboole_0(k1_wellord1(X6,sK4(X6,sK1(sK0,k3_relat_1(X6)))),sK1(sK0,k3_relat_1(X6)))
        | r1_wellord1(sK0,k3_relat_1(X6)) )
    | ~ spl6_0 ),
    inference(subsumption_resolution,[],[f110,f78])).

fof(f78,plain,
    ( ! [X1] :
        ( k1_xboole_0 != sK1(sK0,X1)
        | r1_wellord1(sK0,X1) )
    | ~ spl6_0 ),
    inference(resolution,[],[f73,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != sK1(X0,X1)
      | r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f110,plain,
    ( ! [X6] :
        ( r1_wellord1(sK0,k3_relat_1(X6))
        | ~ v1_relat_1(X6)
        | k1_xboole_0 = sK1(sK0,k3_relat_1(X6))
        | r1_xboole_0(k1_wellord1(X6,sK4(X6,sK1(sK0,k3_relat_1(X6)))),sK1(sK0,k3_relat_1(X6)))
        | ~ v1_wellord1(X6) )
    | ~ spl6_0 ),
    inference(resolution,[],[f77,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X1
      | r1_xboole_0(k1_wellord1(X0,sK4(X0,X1)),X1)
      | ~ v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,
    ( ! [X0] :
        ( r1_tarski(sK1(sK0,X0),X0)
        | r1_wellord1(sK0,X0) )
    | ~ spl6_0 ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(sK1(X0,X1),X1)
      | r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f128,plain,
    ( spl6_10
    | ~ spl6_0
    | ~ spl6_2
    | spl6_5 ),
    inference(avatar_split_clause,[],[f124,f103,f80,f72,f126])).

fof(f124,plain,
    ( r2_hidden(sK4(sK0,sK1(sK0,k3_relat_1(sK0))),sK1(sK0,k3_relat_1(sK0)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f123,f104])).

fof(f123,plain,
    ( r2_hidden(sK4(sK0,sK1(sK0,k3_relat_1(sK0))),sK1(sK0,k3_relat_1(sK0)))
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f122,f73])).

fof(f122,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK4(sK0,sK1(sK0,k3_relat_1(sK0))),sK1(sK0,k3_relat_1(sK0)))
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(resolution,[],[f113,f81])).

fof(f113,plain,
    ( ! [X5] :
        ( ~ v1_wellord1(X5)
        | ~ v1_relat_1(X5)
        | r2_hidden(sK4(X5,sK1(sK0,k3_relat_1(X5))),sK1(sK0,k3_relat_1(X5)))
        | r1_wellord1(sK0,k3_relat_1(X5)) )
    | ~ spl6_0 ),
    inference(subsumption_resolution,[],[f109,f78])).

fof(f109,plain,
    ( ! [X5] :
        ( r1_wellord1(sK0,k3_relat_1(X5))
        | ~ v1_relat_1(X5)
        | k1_xboole_0 = sK1(sK0,k3_relat_1(X5))
        | r2_hidden(sK4(X5,sK1(sK0,k3_relat_1(X5))),sK1(sK0,k3_relat_1(X5)))
        | ~ v1_wellord1(X5) )
    | ~ spl6_0 ),
    inference(resolution,[],[f77,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X1
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f100,plain,
    ( spl6_8
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f88,f83,f72,f98])).

fof(f88,plain,
    ( r1_tarski(sK3(sK0),k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f75,f86])).

fof(f86,plain,
    ( ~ v1_wellord1(sK0)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f44,f84])).

fof(f75,plain,
    ( r1_tarski(sK3(sK0),k3_relat_1(sK0))
    | v1_wellord1(sK0)
    | ~ spl6_0 ),
    inference(resolution,[],[f73,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(sK3(X0),k3_relat_1(X0))
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,
    ( ~ spl6_7
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f87,f83,f72,f94])).

fof(f87,plain,
    ( k1_xboole_0 != sK3(sK0)
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f76,f86])).

fof(f76,plain,
    ( k1_xboole_0 != sK3(sK0)
    | v1_wellord1(sK0)
    | ~ spl6_0 ),
    inference(resolution,[],[f73,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != sK3(X0)
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,
    ( spl6_2
    | spl6_4 ),
    inference(avatar_split_clause,[],[f43,f83,f80])).

fof(f43,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | v1_wellord1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f45,f72])).

fof(f45,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
