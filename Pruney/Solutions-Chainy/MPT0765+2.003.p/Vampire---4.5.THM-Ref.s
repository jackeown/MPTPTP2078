%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 204 expanded)
%              Number of leaves         :   25 (  91 expanded)
%              Depth                    :    7
%              Number of atoms          :  435 ( 866 expanded)
%              Number of equality atoms :   30 (  75 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f45,f50,f55,f59,f63,f67,f71,f75,f84,f92,f109,f115,f122,f130,f143,f148])).

fof(f148,plain,
    ( ~ spl5_5
    | ~ spl5_8
    | ~ spl5_13
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_13
    | spl5_21 ),
    inference(subsumption_resolution,[],[f146,f54])).

fof(f54,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f146,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl5_8
    | ~ spl5_13
    | spl5_21 ),
    inference(subsumption_resolution,[],[f145,f91])).

fof(f91,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_13
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f145,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_8
    | spl5_21 ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_8
    | spl5_21 ),
    inference(resolution,[],[f142,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_8
  <=> ! [X1,X0] :
        ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f142,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_21
  <=> r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f143,plain,
    ( ~ spl5_21
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_19 ),
    inference(avatar_split_clause,[],[f138,f127,f61,f52,f47,f42,f140])).

fof(f42,plain,
    ( spl5_3
  <=> k1_xboole_0 = k3_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f47,plain,
    ( spl5_4
  <=> v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f61,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1),X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f127,plain,
    ( spl5_19
  <=> r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f138,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_19 ),
    inference(subsumption_resolution,[],[f137,f54])).

fof(f137,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_19 ),
    inference(subsumption_resolution,[],[f136,f49])).

fof(f49,plain,
    ( v2_wellord1(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f136,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | spl5_3
    | ~ spl5_7
    | spl5_19 ),
    inference(subsumption_resolution,[],[f135,f44])).

fof(f44,plain,
    ( k1_xboole_0 != k3_relat_1(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f135,plain,
    ( k1_xboole_0 = k3_relat_1(sK0)
    | ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_7
    | spl5_19 ),
    inference(resolution,[],[f129,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f129,plain,
    ( ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f130,plain,
    ( ~ spl5_19
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f125,f120,f38,f34,f127])).

fof(f34,plain,
    ( spl5_1
  <=> ! [X1] :
        ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
        | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f38,plain,
    ( spl5_2
  <=> ! [X1] :
        ( r2_hidden(sK1(X1),k3_relat_1(sK0))
        | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f120,plain,
    ( spl5_18
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(sK0)),X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f125,plain,
    ( ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f123,f39])).

fof(f39,plain,
    ( ! [X1] :
        ( r2_hidden(sK1(X1),k3_relat_1(sK0))
        | ~ r2_hidden(X1,k3_relat_1(sK0)) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f123,plain,
    ( ~ r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_18 ),
    inference(resolution,[],[f121,f35])).

fof(f35,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
        | ~ r2_hidden(X1,k3_relat_1(sK0)) )
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f121,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(sK0)),X0),sK0)
        | ~ r2_hidden(X0,k3_relat_1(sK0)) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl5_18
    | spl5_3
    | ~ spl5_5
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f118,f113,f89,f52,f42,f120])).

fof(f113,plain,
    ( spl5_17
  <=> ! [X1,X0] :
        ( k3_relat_1(X0) = k1_xboole_0
        | ~ r2_hidden(X1,k3_relat_1(X0))
        | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(X0)),X1),sK0)
        | ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(sK0)),X0),sK0) )
    | spl5_3
    | ~ spl5_5
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f117,f54])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(sK0)),X0),sK0)
        | ~ v1_relat_1(sK0) )
    | spl5_3
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f116,f44])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(sK0)),X0),sK0)
        | k1_xboole_0 = k3_relat_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(resolution,[],[f114,f91])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r2_hidden(X1,k3_relat_1(X0))
        | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(X0)),X1),sK0)
        | k3_relat_1(X0) = k1_xboole_0
        | ~ v1_relat_1(X0) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl5_17
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f111,f107,f65,f52,f113])).

fof(f107,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( k3_relat_1(X0) = k1_xboole_0
        | ~ r2_hidden(X1,k3_relat_1(X0))
        | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(X0)),X1),sK0)
        | ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f110,f54])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( k3_relat_1(X0) = k1_xboole_0
        | ~ r2_hidden(X1,k3_relat_1(X0))
        | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(X0)),X1),sK0)
        | ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(resolution,[],[f108,f66])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k3_relat_1(sK0))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X0,X1)
        | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f109,plain,
    ( spl5_16
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f105,f57,f52,f47,f107])).

fof(f57,plain,
    ( spl5_6
  <=> ! [X1,X3,X0] :
        ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
        | ~ r2_hidden(X3,X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | ~ v2_wellord1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f104,f54])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f58,f49])).

fof(f58,plain,
    ( ! [X0,X3,X1] :
        ( ~ v2_wellord1(X0)
        | ~ r2_hidden(X3,X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f92,plain,
    ( spl5_13
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f87,f82,f69,f52,f89])).

fof(f69,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f82,plain,
    ( spl5_12
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK3(sK0,X0),sK4(sK0,X0)),sK0)
        | r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f87,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f86,f54])).

fof(f86,plain,
    ( r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( r1_tarski(sK0,sK0)
    | r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(resolution,[],[f83,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
        | r1_tarski(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f83,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(sK0,X0),sK4(sK0,X0)),sK0)
        | r1_tarski(sK0,X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl5_12
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f80,f73,f52,f82])).

fof(f73,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f80,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(sK0,X0),sK4(sK0,X0)),sK0)
        | r1_tarski(sK0,X0) )
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(resolution,[],[f74,f54])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
        | r1_tarski(X0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f75,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f71,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f63,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK2(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

fof(f59,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X1] :
        ( ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
          & r2_hidden(sK1(X1),k3_relat_1(sK0)) )
        | ~ r2_hidden(X1,k3_relat_1(sK0)) )
    & k1_xboole_0 != k3_relat_1(sK0)
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
        & k3_relat_1(X0) != k1_xboole_0
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
              & r2_hidden(X2,k3_relat_1(sK0)) )
          | ~ r2_hidden(X1,k3_relat_1(sK0)) )
      & k1_xboole_0 != k3_relat_1(sK0)
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
          & r2_hidden(X2,k3_relat_1(sK0)) )
     => ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
        & r2_hidden(sK1(X1),k3_relat_1(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k3_relat_1(X0) != k1_xboole_0
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k3_relat_1(X0) != k1_xboole_0
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k3_relat_1(X0))
                     => r2_hidden(k4_tarski(X1,X2),X0) )
                  & r2_hidden(X1,k3_relat_1(X0)) )
            & k3_relat_1(X0) != k1_xboole_0
            & v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ~ ( ! [X1] :
              ~ ( ! [X2] :
                    ( r2_hidden(X2,k3_relat_1(X0))
                   => r2_hidden(k4_tarski(X1,X2),X0) )
                & r2_hidden(X1,k3_relat_1(X0)) )
          & k3_relat_1(X0) != k1_xboole_0
          & v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).

fof(f50,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    k1_xboole_0 != k3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f25,f38])).

fof(f25,plain,(
    ! [X1] :
      ( r2_hidden(sK1(X1),k3_relat_1(sK0))
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f26,f34])).

fof(f26,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK1(X1)),sK0)
      | ~ r2_hidden(X1,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:23:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (8581)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.43  % (8581)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f149,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f36,f40,f45,f50,f55,f59,f63,f67,f71,f75,f84,f92,f109,f115,f122,f130,f143,f148])).
% 0.20/0.43  fof(f148,plain,(
% 0.20/0.43    ~spl5_5 | ~spl5_8 | ~spl5_13 | spl5_21),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f147])).
% 0.20/0.43  fof(f147,plain,(
% 0.20/0.43    $false | (~spl5_5 | ~spl5_8 | ~spl5_13 | spl5_21)),
% 0.20/0.43    inference(subsumption_resolution,[],[f146,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    v1_relat_1(sK0) | ~spl5_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl5_5 <=> v1_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.43  fof(f146,plain,(
% 0.20/0.43    ~v1_relat_1(sK0) | (~spl5_8 | ~spl5_13 | spl5_21)),
% 0.20/0.43    inference(subsumption_resolution,[],[f145,f91])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    r1_tarski(sK0,sK0) | ~spl5_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f89])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    spl5_13 <=> r1_tarski(sK0,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.43  fof(f145,plain,(
% 0.20/0.43    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK0) | (~spl5_8 | spl5_21)),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f144])).
% 0.20/0.43  fof(f144,plain,(
% 0.20/0.43    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0) | (~spl5_8 | spl5_21)),
% 0.20/0.43    inference(resolution,[],[f142,f66])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl5_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f65])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl5_8 <=> ! [X1,X0] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.43  fof(f142,plain,(
% 0.20/0.43    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | spl5_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f140])).
% 0.20/0.43  fof(f140,plain,(
% 0.20/0.43    spl5_21 <=> r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.43  fof(f143,plain,(
% 0.20/0.43    ~spl5_21 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | spl5_19),
% 0.20/0.43    inference(avatar_split_clause,[],[f138,f127,f61,f52,f47,f42,f140])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl5_3 <=> k1_xboole_0 = k3_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl5_4 <=> v2_wellord1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    spl5_7 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    spl5_19 <=> r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | spl5_19)),
% 0.20/0.43    inference(subsumption_resolution,[],[f137,f54])).
% 0.20/0.43  fof(f137,plain,(
% 0.20/0.43    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (spl5_3 | ~spl5_4 | ~spl5_7 | spl5_19)),
% 0.20/0.43    inference(subsumption_resolution,[],[f136,f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    v2_wellord1(sK0) | ~spl5_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f47])).
% 0.20/0.43  fof(f136,plain,(
% 0.20/0.43    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_relat_1(sK0) | (spl5_3 | ~spl5_7 | spl5_19)),
% 0.20/0.43    inference(subsumption_resolution,[],[f135,f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    k1_xboole_0 != k3_relat_1(sK0) | spl5_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f42])).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    k1_xboole_0 = k3_relat_1(sK0) | ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_relat_1(sK0) | (~spl5_7 | spl5_19)),
% 0.20/0.43    inference(resolution,[],[f129,f62])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) ) | ~spl5_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f61])).
% 0.20/0.43  fof(f129,plain,(
% 0.20/0.43    ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) | spl5_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f127])).
% 0.20/0.43  fof(f130,plain,(
% 0.20/0.43    ~spl5_19 | ~spl5_1 | ~spl5_2 | ~spl5_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f125,f120,f38,f34,f127])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    spl5_1 <=> ! [X1] : (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) | ~r2_hidden(X1,k3_relat_1(sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    spl5_2 <=> ! [X1] : (r2_hidden(sK1(X1),k3_relat_1(sK0)) | ~r2_hidden(X1,k3_relat_1(sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    spl5_18 <=> ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(sK0)),X0),sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_18)),
% 0.20/0.43    inference(subsumption_resolution,[],[f123,f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X1] : (r2_hidden(sK1(X1),k3_relat_1(sK0)) | ~r2_hidden(X1,k3_relat_1(sK0))) ) | ~spl5_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f38])).
% 0.20/0.43  fof(f123,plain,(
% 0.20/0.43    ~r2_hidden(sK1(sK2(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(sK2(sK0,k3_relat_1(sK0)),k3_relat_1(sK0)) | (~spl5_1 | ~spl5_18)),
% 0.20/0.43    inference(resolution,[],[f121,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) | ~r2_hidden(X1,k3_relat_1(sK0))) ) | ~spl5_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f34])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(sK0)),X0),sK0) | ~r2_hidden(X0,k3_relat_1(sK0))) ) | ~spl5_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f120])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    spl5_18 | spl5_3 | ~spl5_5 | ~spl5_13 | ~spl5_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f118,f113,f89,f52,f42,f120])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    spl5_17 <=> ! [X1,X0] : (k3_relat_1(X0) = k1_xboole_0 | ~r2_hidden(X1,k3_relat_1(X0)) | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(X0)),X1),sK0) | ~r1_tarski(X0,sK0) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(sK0)),X0),sK0)) ) | (spl5_3 | ~spl5_5 | ~spl5_13 | ~spl5_17)),
% 0.20/0.43    inference(subsumption_resolution,[],[f117,f54])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(sK0)),X0),sK0) | ~v1_relat_1(sK0)) ) | (spl5_3 | ~spl5_13 | ~spl5_17)),
% 0.20/0.43    inference(subsumption_resolution,[],[f116,f44])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(sK0)),X0),sK0) | k1_xboole_0 = k3_relat_1(sK0) | ~v1_relat_1(sK0)) ) | (~spl5_13 | ~spl5_17)),
% 0.20/0.43    inference(resolution,[],[f114,f91])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,sK0) | ~r2_hidden(X1,k3_relat_1(X0)) | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(X0)),X1),sK0) | k3_relat_1(X0) = k1_xboole_0 | ~v1_relat_1(X0)) ) | ~spl5_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f113])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    spl5_17 | ~spl5_5 | ~spl5_8 | ~spl5_16),
% 0.20/0.43    inference(avatar_split_clause,[],[f111,f107,f65,f52,f113])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    spl5_16 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_relat_1(X0) = k1_xboole_0 | ~r2_hidden(X1,k3_relat_1(X0)) | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(X0)),X1),sK0) | ~r1_tarski(X0,sK0) | ~v1_relat_1(X0)) ) | (~spl5_5 | ~spl5_8 | ~spl5_16)),
% 0.20/0.43    inference(subsumption_resolution,[],[f110,f54])).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_relat_1(X0) = k1_xboole_0 | ~r2_hidden(X1,k3_relat_1(X0)) | r2_hidden(k4_tarski(sK2(sK0,k3_relat_1(X0)),X1),sK0) | ~r1_tarski(X0,sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(X0)) ) | (~spl5_8 | ~spl5_16)),
% 0.20/0.43    inference(resolution,[],[f108,f66])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X1,k3_relat_1(sK0)) | k1_xboole_0 = X1 | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0)) ) | ~spl5_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f107])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    spl5_16 | ~spl5_4 | ~spl5_5 | ~spl5_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f105,f57,f52,f47,f107])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    spl5_6 <=> ! [X1,X3,X0] : (r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.43    inference(subsumption_resolution,[],[f104,f54])).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(sK0,X1),X0),sK0) | ~v1_relat_1(sK0)) ) | (~spl5_4 | ~spl5_6)),
% 0.20/0.43    inference(resolution,[],[f58,f49])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X0,X3,X1] : (~v2_wellord1(X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~v1_relat_1(X0)) ) | ~spl5_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f57])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    spl5_13 | ~spl5_5 | ~spl5_9 | ~spl5_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f87,f82,f69,f52,f89])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl5_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    spl5_12 <=> ! [X0] : (r2_hidden(k4_tarski(sK3(sK0,X0),sK4(sK0,X0)),sK0) | r1_tarski(sK0,X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    r1_tarski(sK0,sK0) | (~spl5_5 | ~spl5_9 | ~spl5_12)),
% 0.20/0.43    inference(subsumption_resolution,[],[f86,f54])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    r1_tarski(sK0,sK0) | ~v1_relat_1(sK0) | (~spl5_9 | ~spl5_12)),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f85])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    r1_tarski(sK0,sK0) | r1_tarski(sK0,sK0) | ~v1_relat_1(sK0) | (~spl5_9 | ~spl5_12)),
% 0.20/0.43    inference(resolution,[],[f83,f70])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) ) | ~spl5_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f69])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(k4_tarski(sK3(sK0,X0),sK4(sK0,X0)),sK0) | r1_tarski(sK0,X0)) ) | ~spl5_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f82])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl5_12 | ~spl5_5 | ~spl5_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f80,f73,f52,f82])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl5_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(k4_tarski(sK3(sK0,X0),sK4(sK0,X0)),sK0) | r1_tarski(sK0,X0)) ) | (~spl5_5 | ~spl5_10)),
% 0.20/0.43    inference(resolution,[],[f74,f54])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r1_tarski(X0,X1)) ) | ~spl5_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f73])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    spl5_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f73])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(rectify,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl5_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f32,f69])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl5_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f65])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(flattening,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    spl5_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f61])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((! [X3] : (r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X1,X0] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X1)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(flattening,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0] : ((! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : (r2_hidden(X3,X1) => r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl5_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f57])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X3,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl5_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f52])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    v1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X1] : ((~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) & r2_hidden(sK1(X1),k3_relat_1(sK0))) | ~r2_hidden(X1,k3_relat_1(sK0))) & k1_xboole_0 != k3_relat_1(sK0) & v2_wellord1(sK0) & v1_relat_1(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ? [X0] : (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0) & v1_relat_1(X0)) => (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),sK0) & r2_hidden(X2,k3_relat_1(sK0))) | ~r2_hidden(X1,k3_relat_1(sK0))) & k1_xboole_0 != k3_relat_1(sK0) & v2_wellord1(sK0) & v1_relat_1(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),sK0) & r2_hidden(X2,k3_relat_1(sK0))) => (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) & r2_hidden(sK1(X1),k3_relat_1(sK0))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ? [X0] : (! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0) & v1_relat_1(X0))),
% 0.20/0.43    inference(flattening,[],[f6])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ? [X0] : ((! [X1] : (? [X2] : (~r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) | ~r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)) & v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (v1_relat_1(X0) => ~(! [X1] : ~(! [X2] : (r2_hidden(X2,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X2),X0)) & r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)))),
% 0.20/0.43    inference(negated_conjecture,[],[f4])).
% 0.20/0.43  fof(f4,conjecture,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ~(! [X1] : ~(! [X2] : (r2_hidden(X2,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X2),X0)) & r2_hidden(X1,k3_relat_1(X0))) & k3_relat_1(X0) != k1_xboole_0 & v2_wellord1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    spl5_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f47])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    v2_wellord1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ~spl5_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f42])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    k1_xboole_0 != k3_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl5_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f38])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X1] : (r2_hidden(sK1(X1),k3_relat_1(sK0)) | ~r2_hidden(X1,k3_relat_1(sK0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    spl5_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f34])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK1(X1)),sK0) | ~r2_hidden(X1,k3_relat_1(sK0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (8581)------------------------------
% 0.20/0.43  % (8581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (8581)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (8581)Memory used [KB]: 10618
% 0.20/0.43  % (8581)Time elapsed: 0.008 s
% 0.20/0.43  % (8581)------------------------------
% 0.20/0.43  % (8581)------------------------------
% 0.20/0.43  % (8576)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.43  % (8574)Success in time 0.072 s
%------------------------------------------------------------------------------
