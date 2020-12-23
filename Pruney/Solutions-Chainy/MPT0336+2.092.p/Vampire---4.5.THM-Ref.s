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
% DateTime   : Thu Dec  3 12:43:36 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 256 expanded)
%              Number of leaves         :   44 ( 120 expanded)
%              Depth                    :    7
%              Number of atoms          :  435 ( 731 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f78,f86,f90,f101,f114,f118,f122,f134,f138,f142,f152,f171,f181,f212,f332,f379,f439,f518,f593,f625,f644,f782,f1050,f2060,f2587,f3263,f3327])).

fof(f3327,plain,
    ( ~ spl6_10
    | ~ spl6_51
    | ~ spl6_59
    | spl6_65
    | ~ spl6_116
    | ~ spl6_137
    | ~ spl6_170 ),
    inference(avatar_contradiction_clause,[],[f3325])).

fof(f3325,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_51
    | ~ spl6_59
    | spl6_65
    | ~ spl6_116
    | ~ spl6_137
    | ~ spl6_170 ),
    inference(subsumption_resolution,[],[f798,f3321])).

fof(f3321,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
    | ~ spl6_10
    | ~ spl6_51
    | ~ spl6_116
    | ~ spl6_137
    | ~ spl6_170 ),
    inference(subsumption_resolution,[],[f2593,f3284])).

fof(f3284,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(X0,sK1),k1_tarski(sK3))
    | ~ spl6_51
    | ~ spl6_116
    | ~ spl6_170 ),
    inference(unit_resulting_resolution,[],[f2059,f3262,f517])).

fof(f517,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f516])).

fof(f516,plain,
    ( spl6_51
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X2,X0)
        | ~ r1_tarski(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f3262,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl6_170 ),
    inference(avatar_component_clause,[],[f3261])).

fof(f3261,plain,
    ( spl6_170
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_170])])).

fof(f2059,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl6_116 ),
    inference(avatar_component_clause,[],[f2057])).

fof(f2057,plain,
    ( spl6_116
  <=> r1_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f2593,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
        | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) )
    | ~ spl6_10
    | ~ spl6_137 ),
    inference(superposition,[],[f100,f2586])).

fof(f2586,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_137 ),
    inference(avatar_component_clause,[],[f2584])).

fof(f2584,plain,
    ( spl6_137
  <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_10
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f798,plain,
    ( r2_hidden(sK4(sK1,sK0),k3_xboole_0(sK0,sK1))
    | ~ spl6_59
    | spl6_65 ),
    inference(unit_resulting_resolution,[],[f781,f643])).

fof(f643,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0))
        | r1_xboole_0(X0,X1) )
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f642])).

fof(f642,plain,
    ( spl6_59
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f781,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_65 ),
    inference(avatar_component_clause,[],[f779])).

fof(f779,plain,
    ( spl6_65
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f3263,plain,
    ( spl6_170
    | ~ spl6_8
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f381,f377,f88,f3261])).

fof(f88,plain,
    ( spl6_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f377,plain,
    ( spl6_40
  <=> ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f381,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl6_8
    | ~ spl6_40 ),
    inference(superposition,[],[f378,f89])).

fof(f89,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f378,plain,
    ( ! [X8,X7] : r1_tarski(k3_xboole_0(X7,X8),X7)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f377])).

fof(f2587,plain,
    ( spl6_137
    | ~ spl6_35
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f594,f591,f330,f2584])).

fof(f330,plain,
    ( spl6_35
  <=> ! [X0] : r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f591,plain,
    ( spl6_54
  <=> ! [X3,X2] :
        ( k3_xboole_0(X2,X3) = X2
        | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f594,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_35
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f331,f592])).

fof(f592,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,k4_xboole_0(X2,X3))
        | k3_xboole_0(X2,X3) = X2 )
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f591])).

fof(f331,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK3)))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f330])).

fof(f2060,plain,
    ( spl6_116
    | ~ spl6_7
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f1190,f1047,f84,f2057])).

fof(f84,plain,
    ( spl6_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1047,plain,
    ( spl6_78
  <=> r1_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1190,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl6_7
    | ~ spl6_78 ),
    inference(unit_resulting_resolution,[],[f1049,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1049,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f1047])).

fof(f1050,plain,
    ( spl6_78
    | ~ spl6_45
    | spl6_56 ),
    inference(avatar_split_clause,[],[f683,f622,f437,f1047])).

fof(f437,plain,
    ( spl6_45
  <=> ! [X7,X8] :
        ( r1_xboole_0(X7,k1_tarski(X8))
        | r2_hidden(X8,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f622,plain,
    ( spl6_56
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f683,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl6_45
    | spl6_56 ),
    inference(unit_resulting_resolution,[],[f624,f438])).

fof(f438,plain,
    ( ! [X8,X7] :
        ( r1_xboole_0(X7,k1_tarski(X8))
        | r2_hidden(X8,X7) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f437])).

fof(f624,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl6_56 ),
    inference(avatar_component_clause,[],[f622])).

fof(f782,plain,
    ( ~ spl6_65
    | ~ spl6_13
    | spl6_23
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f231,f210,f168,f111,f779])).

fof(f111,plain,
    ( spl6_13
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f168,plain,
    ( spl6_23
  <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f210,plain,
    ( spl6_26
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f231,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ spl6_13
    | spl6_23
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f113,f170,f211])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X2) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f210])).

fof(f170,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f168])).

fof(f113,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f644,plain,
    ( spl6_59
    | ~ spl6_8
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f216,f179,f88,f642])).

fof(f179,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0))
        | r1_xboole_0(X0,X1) )
    | ~ spl6_8
    | ~ spl6_24 ),
    inference(superposition,[],[f180,f89])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f179])).

fof(f625,plain,
    ( ~ spl6_56
    | ~ spl6_1
    | ~ spl6_13
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f191,f140,f111,f56,f622])).

fof(f56,plain,
    ( spl6_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f140,plain,
    ( spl6_20
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f191,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl6_1
    | ~ spl6_13
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f113,f58,f141])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f140])).

fof(f58,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f593,plain,
    ( spl6_54
    | ~ spl6_14
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f184,f136,f116,f591])).

fof(f116,plain,
    ( spl6_14
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f136,plain,
    ( spl6_19
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f184,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X2,X3) = X2
        | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) )
    | ~ spl6_14
    | ~ spl6_19 ),
    inference(superposition,[],[f137,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f116])).

fof(f137,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f136])).

fof(f518,plain,
    ( spl6_51
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f177,f132,f116,f516])).

fof(f132,plain,
    ( spl6_18
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X2,X0)
        | ~ r1_tarski(X2,X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(superposition,[],[f133,f117])).

fof(f133,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f132])).

fof(f439,plain,
    ( spl6_45
    | ~ spl6_15
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f203,f150,f120,f437])).

fof(f120,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f150,plain,
    ( spl6_22
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f203,plain,
    ( ! [X8,X7] :
        ( r1_xboole_0(X7,k1_tarski(X8))
        | r2_hidden(X8,X7) )
    | ~ spl6_15
    | ~ spl6_22 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( ! [X8,X7] :
        ( X7 != X7
        | r1_xboole_0(X7,k1_tarski(X8))
        | r2_hidden(X8,X7) )
    | ~ spl6_15
    | ~ spl6_22 ),
    inference(superposition,[],[f121,f151])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f150])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f379,plain,
    ( spl6_40
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f188,f136,f76,f377])).

fof(f76,plain,
    ( spl6_5
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f188,plain,
    ( ! [X8,X7] : r1_tarski(k3_xboole_0(X7,X8),X7)
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(superposition,[],[f77,f137])).

fof(f77,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f332,plain,
    ( spl6_35
    | ~ spl6_4
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f174,f132,f71,f330])).

fof(f71,plain,
    ( spl6_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f174,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK3)))
    | ~ spl6_4
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f73,f133])).

fof(f73,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f212,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f51,f210])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f181,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f41,f179])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f171,plain,
    ( ~ spl6_23
    | spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f91,f84,f66,f168])).

fof(f66,plain,
    ( spl6_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f91,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl6_3
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f68,f85])).

fof(f68,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f152,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f50,f150])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f142,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f45,f140])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f138,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f40,f136])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f134,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f54,f132])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f122,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f48,f120])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f118,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f47,f116])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,
    ( spl6_13
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f92,f84,f61,f111])).

fof(f61,plain,
    ( spl6_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f92,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f63,f85])).

fof(f63,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f101,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f38,f88])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f86,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f46,f84])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f78,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f37,f76])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f74,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f69,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f33,f56])).

fof(f33,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:24:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (13571)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (13562)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (13572)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (13557)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (13564)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (13568)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (13559)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (13560)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (13569)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (13565)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (13566)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (13570)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (13563)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (13558)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (13561)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (13567)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (13574)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (13573)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.76/0.59  % (13562)Refutation found. Thanks to Tanya!
% 1.76/0.59  % SZS status Theorem for theBenchmark
% 1.76/0.59  % SZS output start Proof for theBenchmark
% 1.76/0.59  fof(f3329,plain,(
% 1.76/0.59    $false),
% 1.76/0.59    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f78,f86,f90,f101,f114,f118,f122,f134,f138,f142,f152,f171,f181,f212,f332,f379,f439,f518,f593,f625,f644,f782,f1050,f2060,f2587,f3263,f3327])).
% 1.76/0.59  fof(f3327,plain,(
% 1.76/0.59    ~spl6_10 | ~spl6_51 | ~spl6_59 | spl6_65 | ~spl6_116 | ~spl6_137 | ~spl6_170),
% 1.76/0.59    inference(avatar_contradiction_clause,[],[f3325])).
% 1.76/0.59  fof(f3325,plain,(
% 1.76/0.59    $false | (~spl6_10 | ~spl6_51 | ~spl6_59 | spl6_65 | ~spl6_116 | ~spl6_137 | ~spl6_170)),
% 1.76/0.59    inference(subsumption_resolution,[],[f798,f3321])).
% 1.76/0.59  fof(f3321,plain,(
% 1.76/0.59    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1))) ) | (~spl6_10 | ~spl6_51 | ~spl6_116 | ~spl6_137 | ~spl6_170)),
% 1.76/0.59    inference(subsumption_resolution,[],[f2593,f3284])).
% 1.76/0.59  fof(f3284,plain,(
% 1.76/0.59    ( ! [X0] : (r1_xboole_0(k3_xboole_0(X0,sK1),k1_tarski(sK3))) ) | (~spl6_51 | ~spl6_116 | ~spl6_170)),
% 1.76/0.59    inference(unit_resulting_resolution,[],[f2059,f3262,f517])).
% 1.76/0.59  fof(f517,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_xboole_0(X2,X0) | ~r1_xboole_0(X0,X1)) ) | ~spl6_51),
% 1.76/0.59    inference(avatar_component_clause,[],[f516])).
% 1.76/0.59  fof(f516,plain,(
% 1.76/0.59    spl6_51 <=> ! [X1,X0,X2] : (r1_xboole_0(X2,X0) | ~r1_tarski(X2,X1) | ~r1_xboole_0(X0,X1))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 1.76/0.59  fof(f3262,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | ~spl6_170),
% 1.76/0.59    inference(avatar_component_clause,[],[f3261])).
% 1.76/0.59  fof(f3261,plain,(
% 1.76/0.59    spl6_170 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_170])])).
% 1.76/0.59  fof(f2059,plain,(
% 1.76/0.59    r1_xboole_0(k1_tarski(sK3),sK1) | ~spl6_116),
% 1.76/0.59    inference(avatar_component_clause,[],[f2057])).
% 1.76/0.59  fof(f2057,plain,(
% 1.76/0.59    spl6_116 <=> r1_xboole_0(k1_tarski(sK3),sK1)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).
% 1.76/0.59  fof(f2593,plain,(
% 1.76/0.59    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))) ) | (~spl6_10 | ~spl6_137)),
% 1.76/0.59    inference(superposition,[],[f100,f2586])).
% 1.76/0.59  fof(f2586,plain,(
% 1.76/0.59    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl6_137),
% 1.76/0.59    inference(avatar_component_clause,[],[f2584])).
% 1.76/0.59  fof(f2584,plain,(
% 1.76/0.59    spl6_137 <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).
% 1.76/0.59  fof(f100,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl6_10),
% 1.76/0.59    inference(avatar_component_clause,[],[f99])).
% 1.76/0.59  fof(f99,plain,(
% 1.76/0.59    spl6_10 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.76/0.59  fof(f798,plain,(
% 1.76/0.59    r2_hidden(sK4(sK1,sK0),k3_xboole_0(sK0,sK1)) | (~spl6_59 | spl6_65)),
% 1.76/0.59    inference(unit_resulting_resolution,[],[f781,f643])).
% 1.76/0.59  fof(f643,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1)) ) | ~spl6_59),
% 1.76/0.59    inference(avatar_component_clause,[],[f642])).
% 1.76/0.59  fof(f642,plain,(
% 1.76/0.59    spl6_59 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 1.76/0.59  fof(f781,plain,(
% 1.76/0.59    ~r1_xboole_0(sK1,sK0) | spl6_65),
% 1.76/0.59    inference(avatar_component_clause,[],[f779])).
% 1.76/0.59  fof(f779,plain,(
% 1.76/0.59    spl6_65 <=> r1_xboole_0(sK1,sK0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 1.76/0.59  fof(f3263,plain,(
% 1.76/0.59    spl6_170 | ~spl6_8 | ~spl6_40),
% 1.76/0.59    inference(avatar_split_clause,[],[f381,f377,f88,f3261])).
% 1.76/0.59  fof(f88,plain,(
% 1.76/0.59    spl6_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.76/0.59  fof(f377,plain,(
% 1.76/0.59    spl6_40 <=> ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.76/0.59  fof(f381,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl6_8 | ~spl6_40)),
% 1.76/0.59    inference(superposition,[],[f378,f89])).
% 1.76/0.59  fof(f89,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl6_8),
% 1.76/0.59    inference(avatar_component_clause,[],[f88])).
% 1.76/0.59  fof(f378,plain,(
% 1.76/0.59    ( ! [X8,X7] : (r1_tarski(k3_xboole_0(X7,X8),X7)) ) | ~spl6_40),
% 1.76/0.59    inference(avatar_component_clause,[],[f377])).
% 1.76/0.59  fof(f2587,plain,(
% 1.76/0.59    spl6_137 | ~spl6_35 | ~spl6_54),
% 1.76/0.59    inference(avatar_split_clause,[],[f594,f591,f330,f2584])).
% 1.76/0.59  fof(f330,plain,(
% 1.76/0.59    spl6_35 <=> ! [X0] : r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK3)))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.76/0.59  fof(f591,plain,(
% 1.76/0.59    spl6_54 <=> ! [X3,X2] : (k3_xboole_0(X2,X3) = X2 | ~r1_xboole_0(X2,k4_xboole_0(X2,X3)))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 1.76/0.59  fof(f594,plain,(
% 1.76/0.59    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | (~spl6_35 | ~spl6_54)),
% 1.76/0.59    inference(unit_resulting_resolution,[],[f331,f592])).
% 1.76/0.59  fof(f592,plain,(
% 1.76/0.59    ( ! [X2,X3] : (~r1_xboole_0(X2,k4_xboole_0(X2,X3)) | k3_xboole_0(X2,X3) = X2) ) | ~spl6_54),
% 1.76/0.59    inference(avatar_component_clause,[],[f591])).
% 1.76/0.59  fof(f331,plain,(
% 1.76/0.59    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK3)))) ) | ~spl6_35),
% 1.76/0.59    inference(avatar_component_clause,[],[f330])).
% 1.76/0.59  fof(f2060,plain,(
% 1.76/0.59    spl6_116 | ~spl6_7 | ~spl6_78),
% 1.76/0.59    inference(avatar_split_clause,[],[f1190,f1047,f84,f2057])).
% 1.76/0.59  fof(f84,plain,(
% 1.76/0.59    spl6_7 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.76/0.59  fof(f1047,plain,(
% 1.76/0.59    spl6_78 <=> r1_xboole_0(sK1,k1_tarski(sK3))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 1.76/0.59  fof(f1190,plain,(
% 1.76/0.59    r1_xboole_0(k1_tarski(sK3),sK1) | (~spl6_7 | ~spl6_78)),
% 1.76/0.59    inference(unit_resulting_resolution,[],[f1049,f85])).
% 1.76/0.59  fof(f85,plain,(
% 1.76/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl6_7),
% 1.76/0.59    inference(avatar_component_clause,[],[f84])).
% 1.76/0.59  fof(f1049,plain,(
% 1.76/0.59    r1_xboole_0(sK1,k1_tarski(sK3)) | ~spl6_78),
% 1.76/0.59    inference(avatar_component_clause,[],[f1047])).
% 1.76/0.59  fof(f1050,plain,(
% 1.76/0.59    spl6_78 | ~spl6_45 | spl6_56),
% 1.76/0.59    inference(avatar_split_clause,[],[f683,f622,f437,f1047])).
% 1.76/0.59  fof(f437,plain,(
% 1.76/0.59    spl6_45 <=> ! [X7,X8] : (r1_xboole_0(X7,k1_tarski(X8)) | r2_hidden(X8,X7))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 1.76/0.59  fof(f622,plain,(
% 1.76/0.59    spl6_56 <=> r2_hidden(sK3,sK1)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 1.76/0.59  fof(f683,plain,(
% 1.76/0.59    r1_xboole_0(sK1,k1_tarski(sK3)) | (~spl6_45 | spl6_56)),
% 1.76/0.59    inference(unit_resulting_resolution,[],[f624,f438])).
% 1.76/0.59  fof(f438,plain,(
% 1.76/0.59    ( ! [X8,X7] : (r1_xboole_0(X7,k1_tarski(X8)) | r2_hidden(X8,X7)) ) | ~spl6_45),
% 1.76/0.59    inference(avatar_component_clause,[],[f437])).
% 1.76/0.59  fof(f624,plain,(
% 1.76/0.59    ~r2_hidden(sK3,sK1) | spl6_56),
% 1.76/0.59    inference(avatar_component_clause,[],[f622])).
% 1.76/0.59  fof(f782,plain,(
% 1.76/0.59    ~spl6_65 | ~spl6_13 | spl6_23 | ~spl6_26),
% 1.76/0.59    inference(avatar_split_clause,[],[f231,f210,f168,f111,f779])).
% 1.76/0.59  fof(f111,plain,(
% 1.76/0.59    spl6_13 <=> r1_xboole_0(sK1,sK2)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.76/0.59  fof(f168,plain,(
% 1.76/0.59    spl6_23 <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.76/0.59  fof(f210,plain,(
% 1.76/0.59    spl6_26 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.76/0.59  fof(f231,plain,(
% 1.76/0.59    ~r1_xboole_0(sK1,sK0) | (~spl6_13 | spl6_23 | ~spl6_26)),
% 1.76/0.59    inference(unit_resulting_resolution,[],[f113,f170,f211])).
% 1.76/0.59  fof(f211,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) ) | ~spl6_26),
% 1.76/0.59    inference(avatar_component_clause,[],[f210])).
% 1.76/0.59  fof(f170,plain,(
% 1.76/0.59    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | spl6_23),
% 1.76/0.59    inference(avatar_component_clause,[],[f168])).
% 1.76/0.59  fof(f113,plain,(
% 1.76/0.59    r1_xboole_0(sK1,sK2) | ~spl6_13),
% 1.76/0.59    inference(avatar_component_clause,[],[f111])).
% 1.76/0.59  fof(f644,plain,(
% 1.76/0.59    spl6_59 | ~spl6_8 | ~spl6_24),
% 1.76/0.59    inference(avatar_split_clause,[],[f216,f179,f88,f642])).
% 1.76/0.59  fof(f179,plain,(
% 1.76/0.59    spl6_24 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.76/0.59  fof(f216,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1)) ) | (~spl6_8 | ~spl6_24)),
% 1.76/0.59    inference(superposition,[],[f180,f89])).
% 1.76/0.59  fof(f180,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | ~spl6_24),
% 1.76/0.59    inference(avatar_component_clause,[],[f179])).
% 1.76/0.59  fof(f625,plain,(
% 1.76/0.59    ~spl6_56 | ~spl6_1 | ~spl6_13 | ~spl6_20),
% 1.76/0.59    inference(avatar_split_clause,[],[f191,f140,f111,f56,f622])).
% 1.76/0.59  fof(f56,plain,(
% 1.76/0.59    spl6_1 <=> r2_hidden(sK3,sK2)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.76/0.59  fof(f140,plain,(
% 1.76/0.59    spl6_20 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.76/0.59  fof(f191,plain,(
% 1.76/0.59    ~r2_hidden(sK3,sK1) | (~spl6_1 | ~spl6_13 | ~spl6_20)),
% 1.76/0.59    inference(unit_resulting_resolution,[],[f113,f58,f141])).
% 1.76/0.59  fof(f141,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) ) | ~spl6_20),
% 1.76/0.59    inference(avatar_component_clause,[],[f140])).
% 1.76/0.59  fof(f58,plain,(
% 1.76/0.59    r2_hidden(sK3,sK2) | ~spl6_1),
% 1.76/0.59    inference(avatar_component_clause,[],[f56])).
% 1.76/0.59  fof(f593,plain,(
% 1.76/0.59    spl6_54 | ~spl6_14 | ~spl6_19),
% 1.76/0.59    inference(avatar_split_clause,[],[f184,f136,f116,f591])).
% 1.76/0.59  fof(f116,plain,(
% 1.76/0.59    spl6_14 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.76/0.59  fof(f136,plain,(
% 1.76/0.59    spl6_19 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.76/0.59  fof(f184,plain,(
% 1.76/0.59    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X2 | ~r1_xboole_0(X2,k4_xboole_0(X2,X3))) ) | (~spl6_14 | ~spl6_19)),
% 1.76/0.59    inference(superposition,[],[f137,f117])).
% 1.76/0.59  fof(f117,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl6_14),
% 1.76/0.59    inference(avatar_component_clause,[],[f116])).
% 1.76/0.59  fof(f137,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl6_19),
% 1.76/0.59    inference(avatar_component_clause,[],[f136])).
% 1.76/0.59  fof(f518,plain,(
% 1.76/0.59    spl6_51 | ~spl6_14 | ~spl6_18),
% 1.76/0.59    inference(avatar_split_clause,[],[f177,f132,f116,f516])).
% 1.76/0.59  fof(f132,plain,(
% 1.76/0.59    spl6_18 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.76/0.59  fof(f177,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(X2,X0) | ~r1_tarski(X2,X1) | ~r1_xboole_0(X0,X1)) ) | (~spl6_14 | ~spl6_18)),
% 1.76/0.59    inference(superposition,[],[f133,f117])).
% 1.76/0.59  fof(f133,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl6_18),
% 1.76/0.59    inference(avatar_component_clause,[],[f132])).
% 1.76/0.59  fof(f439,plain,(
% 1.76/0.59    spl6_45 | ~spl6_15 | ~spl6_22),
% 1.76/0.59    inference(avatar_split_clause,[],[f203,f150,f120,f437])).
% 1.76/0.59  fof(f120,plain,(
% 1.76/0.59    spl6_15 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.76/0.59  fof(f150,plain,(
% 1.76/0.59    spl6_22 <=> ! [X1,X0] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.76/0.59  fof(f203,plain,(
% 1.76/0.59    ( ! [X8,X7] : (r1_xboole_0(X7,k1_tarski(X8)) | r2_hidden(X8,X7)) ) | (~spl6_15 | ~spl6_22)),
% 1.76/0.59    inference(trivial_inequality_removal,[],[f201])).
% 1.76/0.59  fof(f201,plain,(
% 1.76/0.59    ( ! [X8,X7] : (X7 != X7 | r1_xboole_0(X7,k1_tarski(X8)) | r2_hidden(X8,X7)) ) | (~spl6_15 | ~spl6_22)),
% 1.76/0.59    inference(superposition,[],[f121,f151])).
% 1.76/0.59  fof(f151,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) ) | ~spl6_22),
% 1.76/0.59    inference(avatar_component_clause,[],[f150])).
% 1.76/0.59  fof(f121,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl6_15),
% 1.76/0.59    inference(avatar_component_clause,[],[f120])).
% 1.76/0.59  fof(f379,plain,(
% 1.76/0.59    spl6_40 | ~spl6_5 | ~spl6_19),
% 1.76/0.59    inference(avatar_split_clause,[],[f188,f136,f76,f377])).
% 1.76/0.59  fof(f76,plain,(
% 1.76/0.59    spl6_5 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.76/0.59  fof(f188,plain,(
% 1.76/0.59    ( ! [X8,X7] : (r1_tarski(k3_xboole_0(X7,X8),X7)) ) | (~spl6_5 | ~spl6_19)),
% 1.76/0.59    inference(superposition,[],[f77,f137])).
% 1.76/0.59  fof(f77,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl6_5),
% 1.76/0.59    inference(avatar_component_clause,[],[f76])).
% 1.76/0.59  fof(f332,plain,(
% 1.76/0.59    spl6_35 | ~spl6_4 | ~spl6_18),
% 1.76/0.59    inference(avatar_split_clause,[],[f174,f132,f71,f330])).
% 1.76/0.59  fof(f71,plain,(
% 1.76/0.59    spl6_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.76/0.59  fof(f174,plain,(
% 1.76/0.59    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK3)))) ) | (~spl6_4 | ~spl6_18)),
% 1.76/0.59    inference(unit_resulting_resolution,[],[f73,f133])).
% 1.76/0.59  fof(f73,plain,(
% 1.76/0.59    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl6_4),
% 1.76/0.59    inference(avatar_component_clause,[],[f71])).
% 1.76/0.59  fof(f212,plain,(
% 1.76/0.59    spl6_26),
% 1.76/0.59    inference(avatar_split_clause,[],[f51,f210])).
% 1.76/0.59  fof(f51,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.76/0.59    inference(cnf_transformation,[],[f22])).
% 1.76/0.59  fof(f22,plain,(
% 1.76/0.59    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.76/0.59    inference(ennf_transformation,[],[f7])).
% 1.76/0.59  fof(f7,axiom,(
% 1.76/0.59    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.76/0.59  fof(f181,plain,(
% 1.76/0.59    spl6_24),
% 1.76/0.59    inference(avatar_split_clause,[],[f41,f179])).
% 1.76/0.59  fof(f41,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f27])).
% 1.76/0.59  fof(f27,plain,(
% 1.76/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.76/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f26])).
% 1.76/0.59  fof(f26,plain,(
% 1.76/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.76/0.59    introduced(choice_axiom,[])).
% 1.76/0.59  fof(f19,plain,(
% 1.76/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.76/0.59    inference(ennf_transformation,[],[f15])).
% 1.76/0.59  fof(f15,plain,(
% 1.76/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.76/0.59    inference(rectify,[],[f4])).
% 1.76/0.59  fof(f4,axiom,(
% 1.76/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.76/0.59  fof(f171,plain,(
% 1.76/0.59    ~spl6_23 | spl6_3 | ~spl6_7),
% 1.76/0.59    inference(avatar_split_clause,[],[f91,f84,f66,f168])).
% 1.76/0.59  fof(f66,plain,(
% 1.76/0.59    spl6_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.76/0.59  fof(f91,plain,(
% 1.76/0.59    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | (spl6_3 | ~spl6_7)),
% 1.76/0.59    inference(unit_resulting_resolution,[],[f68,f85])).
% 1.76/0.59  fof(f68,plain,(
% 1.76/0.59    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl6_3),
% 1.76/0.59    inference(avatar_component_clause,[],[f66])).
% 1.76/0.59  fof(f152,plain,(
% 1.76/0.59    spl6_22),
% 1.76/0.59    inference(avatar_split_clause,[],[f50,f150])).
% 1.76/0.59  fof(f50,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f31])).
% 1.76/0.59  fof(f31,plain,(
% 1.76/0.59    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.76/0.59    inference(nnf_transformation,[],[f12])).
% 1.76/0.59  fof(f12,axiom,(
% 1.76/0.59    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.76/0.59  fof(f142,plain,(
% 1.76/0.59    spl6_20),
% 1.76/0.59    inference(avatar_split_clause,[],[f45,f140])).
% 1.76/0.59  fof(f45,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f29])).
% 1.76/0.59  fof(f29,plain,(
% 1.76/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.76/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f28])).
% 1.76/0.59  fof(f28,plain,(
% 1.76/0.59    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.76/0.59    introduced(choice_axiom,[])).
% 1.76/0.59  fof(f20,plain,(
% 1.76/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.76/0.59    inference(ennf_transformation,[],[f16])).
% 1.76/0.59  fof(f16,plain,(
% 1.76/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.76/0.59    inference(rectify,[],[f3])).
% 1.76/0.59  fof(f3,axiom,(
% 1.76/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.76/0.59  fof(f138,plain,(
% 1.76/0.59    spl6_19),
% 1.76/0.59    inference(avatar_split_clause,[],[f40,f136])).
% 1.76/0.59  fof(f40,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.76/0.59    inference(cnf_transformation,[],[f6])).
% 1.76/0.59  fof(f6,axiom,(
% 1.76/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.76/0.59  fof(f134,plain,(
% 1.76/0.59    spl6_18),
% 1.76/0.59    inference(avatar_split_clause,[],[f54,f132])).
% 1.76/0.59  fof(f54,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f23])).
% 1.76/0.59  fof(f23,plain,(
% 1.76/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.76/0.59    inference(ennf_transformation,[],[f9])).
% 1.76/0.59  fof(f9,axiom,(
% 1.76/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.76/0.59  fof(f122,plain,(
% 1.76/0.59    spl6_15),
% 1.76/0.59    inference(avatar_split_clause,[],[f48,f120])).
% 1.76/0.59  fof(f48,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.76/0.59    inference(cnf_transformation,[],[f30])).
% 1.76/0.59  fof(f30,plain,(
% 1.76/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.76/0.59    inference(nnf_transformation,[],[f8])).
% 1.76/0.59  fof(f8,axiom,(
% 1.76/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.76/0.59  fof(f118,plain,(
% 1.76/0.59    spl6_14),
% 1.76/0.59    inference(avatar_split_clause,[],[f47,f116])).
% 1.76/0.59  fof(f47,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f30])).
% 1.76/0.59  fof(f114,plain,(
% 1.76/0.59    spl6_13 | ~spl6_2 | ~spl6_7),
% 1.76/0.59    inference(avatar_split_clause,[],[f92,f84,f61,f111])).
% 1.76/0.59  fof(f61,plain,(
% 1.76/0.59    spl6_2 <=> r1_xboole_0(sK2,sK1)),
% 1.76/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.76/0.59  fof(f92,plain,(
% 1.76/0.59    r1_xboole_0(sK1,sK2) | (~spl6_2 | ~spl6_7)),
% 1.76/0.59    inference(unit_resulting_resolution,[],[f63,f85])).
% 1.76/0.59  fof(f63,plain,(
% 1.76/0.59    r1_xboole_0(sK2,sK1) | ~spl6_2),
% 1.76/0.59    inference(avatar_component_clause,[],[f61])).
% 1.76/0.59  fof(f101,plain,(
% 1.76/0.59    spl6_10),
% 1.76/0.59    inference(avatar_split_clause,[],[f42,f99])).
% 1.76/0.59  fof(f42,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.76/0.59    inference(cnf_transformation,[],[f27])).
% 1.76/0.59  fof(f90,plain,(
% 1.76/0.59    spl6_8),
% 1.76/0.59    inference(avatar_split_clause,[],[f38,f88])).
% 1.76/0.59  fof(f38,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f1])).
% 1.76/0.59  fof(f1,axiom,(
% 1.76/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.76/0.59  fof(f86,plain,(
% 1.76/0.59    spl6_7),
% 1.76/0.59    inference(avatar_split_clause,[],[f46,f84])).
% 1.76/0.59  fof(f46,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f21])).
% 1.76/0.59  fof(f21,plain,(
% 1.76/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.76/0.59    inference(ennf_transformation,[],[f2])).
% 1.76/0.59  fof(f2,axiom,(
% 1.76/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.76/0.59  fof(f78,plain,(
% 1.76/0.59    spl6_5),
% 1.76/0.59    inference(avatar_split_clause,[],[f37,f76])).
% 1.76/0.59  fof(f37,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f5])).
% 1.76/0.59  fof(f5,axiom,(
% 1.76/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.76/0.59  fof(f74,plain,(
% 1.76/0.59    spl6_4),
% 1.76/0.59    inference(avatar_split_clause,[],[f32,f71])).
% 1.76/0.59  fof(f32,plain,(
% 1.76/0.59    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.76/0.59    inference(cnf_transformation,[],[f25])).
% 1.76/0.59  fof(f25,plain,(
% 1.76/0.59    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.76/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f24])).
% 1.76/0.59  fof(f24,plain,(
% 1.76/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.76/0.59    introduced(choice_axiom,[])).
% 1.76/0.59  fof(f18,plain,(
% 1.76/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.76/0.59    inference(flattening,[],[f17])).
% 1.76/0.59  fof(f17,plain,(
% 1.76/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.76/0.59    inference(ennf_transformation,[],[f14])).
% 1.76/0.59  fof(f14,negated_conjecture,(
% 1.76/0.59    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.76/0.59    inference(negated_conjecture,[],[f13])).
% 1.76/0.59  fof(f13,conjecture,(
% 1.76/0.59    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.76/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.76/0.59  fof(f69,plain,(
% 1.76/0.59    ~spl6_3),
% 1.76/0.59    inference(avatar_split_clause,[],[f35,f66])).
% 1.76/0.59  fof(f35,plain,(
% 1.76/0.59    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.76/0.59    inference(cnf_transformation,[],[f25])).
% 1.76/0.59  fof(f64,plain,(
% 1.76/0.59    spl6_2),
% 1.76/0.59    inference(avatar_split_clause,[],[f34,f61])).
% 1.76/0.59  fof(f34,plain,(
% 1.76/0.59    r1_xboole_0(sK2,sK1)),
% 1.76/0.59    inference(cnf_transformation,[],[f25])).
% 1.76/0.59  fof(f59,plain,(
% 1.76/0.59    spl6_1),
% 1.76/0.59    inference(avatar_split_clause,[],[f33,f56])).
% 1.76/0.59  fof(f33,plain,(
% 1.76/0.59    r2_hidden(sK3,sK2)),
% 1.76/0.59    inference(cnf_transformation,[],[f25])).
% 1.76/0.59  % SZS output end Proof for theBenchmark
% 1.76/0.59  % (13562)------------------------------
% 1.76/0.59  % (13562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.59  % (13562)Termination reason: Refutation
% 1.76/0.59  
% 1.76/0.59  % (13562)Memory used [KB]: 8443
% 1.76/0.59  % (13562)Time elapsed: 0.151 s
% 1.76/0.59  % (13562)------------------------------
% 1.76/0.59  % (13562)------------------------------
% 1.76/0.59  % (13556)Success in time 0.224 s
%------------------------------------------------------------------------------
