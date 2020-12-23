%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0565+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 137 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :    6
%              Number of atoms          :  278 ( 477 expanded)
%              Number of equality atoms :   46 (  85 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f342,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f46,f62,f66,f70,f84,f171,f188,f206,f225,f278,f307,f327,f340])).

fof(f340,plain,
    ( ~ spl10_1
    | ~ spl10_9
    | ~ spl10_39
    | ~ spl10_42 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_9
    | ~ spl10_39
    | ~ spl10_42 ),
    inference(unit_resulting_resolution,[],[f33,f306,f326,f65])).

fof(f65,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(k4_tarski(X3,sK2(X0,X1,X3)),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) )
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl10_9
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X3,sK2(X0,X1,X3)),X0)
        | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f326,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl10_42
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK4(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f306,plain,
    ( r2_hidden(sK4(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0)))
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl10_39
  <=> r2_hidden(sK4(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f33,plain,
    ( v1_relat_1(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl10_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f327,plain,
    ( spl10_42
    | spl10_2
    | ~ spl10_10
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f313,f305,f68,f36,f325])).

fof(f36,plain,
    ( spl10_2
  <=> k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f68,plain,
    ( spl10_10
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
        | ~ r2_hidden(sK4(X0,X1),X1)
        | k1_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f313,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)
    | spl10_2
    | ~ spl10_10
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f312,f37])).

fof(f37,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f312,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0)
        | k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) )
    | ~ spl10_10
    | ~ spl10_39 ),
    inference(resolution,[],[f306,f69])).

fof(f69,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(sK4(X0,X1),X1)
        | ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
        | k1_relat_1(X0) = X1 )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f307,plain,
    ( spl10_39
    | spl10_2
    | ~ spl10_12
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f289,f276,f82,f36,f305])).

fof(f82,plain,
    ( spl10_12
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
        | r2_hidden(sK4(X0,X1),X1)
        | k1_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f276,plain,
    ( spl10_37
  <=> ! [X3,X2] :
        ( k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X3,sK6(sK0,k10_relat_1(sK0,k2_relat_1(X2)))),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f289,plain,
    ( r2_hidden(sK4(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0)))
    | spl10_2
    | ~ spl10_12
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f288,f37])).

fof(f288,plain,
    ( k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))
    | r2_hidden(sK4(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0)))
    | ~ spl10_12
    | ~ spl10_37 ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,
    ( k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))
    | r2_hidden(sK4(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0)))
    | k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))
    | ~ spl10_12
    | ~ spl10_37 ),
    inference(resolution,[],[f277,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
        | r2_hidden(sK4(X0,X1),X1)
        | k1_relat_1(X0) = X1 )
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f277,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X3,sK6(sK0,k10_relat_1(sK0,k2_relat_1(X2)))),X2)
        | k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(X2)) )
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f276])).

fof(f278,plain,
    ( spl10_37
    | ~ spl10_4
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f235,f223,f44,f276])).

fof(f44,plain,
    ( spl10_4
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X3,X2),X0)
        | r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f223,plain,
    ( spl10_32
  <=> ! [X3] :
        ( ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X3)),X3)
        | k1_relat_1(sK0) = k10_relat_1(sK0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f235,plain,
    ( ! [X2,X3] :
        ( k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X3,sK6(sK0,k10_relat_1(sK0,k2_relat_1(X2)))),X2) )
    | ~ spl10_4
    | ~ spl10_32 ),
    inference(resolution,[],[f224,f45])).

fof(f45,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k2_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X3,X2),X0) )
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f224,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X3)),X3)
        | k1_relat_1(sK0) = k10_relat_1(sK0,X3) )
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( spl10_32
    | ~ spl10_1
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f216,f204,f82,f64,f32,f223])).

fof(f204,plain,
    ( spl10_29
  <=> ! [X7,X8] :
        ( k1_relat_1(sK0) = k10_relat_1(sK0,X7)
        | ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X7)),X7)
        | ~ r2_hidden(k4_tarski(sK4(sK0,k10_relat_1(sK0,X7)),X8),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f216,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X3)),X3)
        | k1_relat_1(sK0) = k10_relat_1(sK0,X3) )
    | ~ spl10_1
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f214,f215])).

fof(f215,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X1)),X1)
        | k1_relat_1(sK0) = k10_relat_1(sK0,X1)
        | ~ r2_hidden(sK4(sK0,k10_relat_1(sK0,X1)),k10_relat_1(sK0,X2)) )
    | ~ spl10_1
    | ~ spl10_9
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f212,f33])).

fof(f212,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X1)),X1)
        | k1_relat_1(sK0) = k10_relat_1(sK0,X1)
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(sK4(sK0,k10_relat_1(sK0,X1)),k10_relat_1(sK0,X2)) )
    | ~ spl10_9
    | ~ spl10_29 ),
    inference(resolution,[],[f205,f65])).

fof(f205,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(k4_tarski(sK4(sK0,k10_relat_1(sK0,X7)),X8),sK0)
        | ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X7)),X7)
        | k1_relat_1(sK0) = k10_relat_1(sK0,X7) )
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f204])).

fof(f214,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X3)),X3)
        | k1_relat_1(sK0) = k10_relat_1(sK0,X3)
        | r2_hidden(sK4(sK0,k10_relat_1(sK0,X3)),k10_relat_1(sK0,X3)) )
    | ~ spl10_12
    | ~ spl10_29 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X3)),X3)
        | k1_relat_1(sK0) = k10_relat_1(sK0,X3)
        | r2_hidden(sK4(sK0,k10_relat_1(sK0,X3)),k10_relat_1(sK0,X3))
        | k1_relat_1(sK0) = k10_relat_1(sK0,X3) )
    | ~ spl10_12
    | ~ spl10_29 ),
    inference(resolution,[],[f205,f83])).

fof(f206,plain,
    ( spl10_29
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f195,f186,f82,f68,f204])).

fof(f186,plain,
    ( spl10_27
  <=> ! [X1,X3,X0,X2] :
        ( k1_relat_1(X1) = k10_relat_1(sK0,X0)
        | ~ r2_hidden(k4_tarski(sK4(X1,k10_relat_1(sK0,X0)),X2),sK0)
        | ~ r2_hidden(X2,X0)
        | ~ r2_hidden(k4_tarski(sK4(X1,k10_relat_1(sK0,X0)),X3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f195,plain,
    ( ! [X8,X7] :
        ( k1_relat_1(sK0) = k10_relat_1(sK0,X7)
        | ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X7)),X7)
        | ~ r2_hidden(k4_tarski(sK4(sK0,k10_relat_1(sK0,X7)),X8),sK0) )
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f193,f69])).

fof(f193,plain,
    ( ! [X8,X7] :
        ( k1_relat_1(sK0) = k10_relat_1(sK0,X7)
        | ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X7)),X7)
        | ~ r2_hidden(k4_tarski(sK4(sK0,k10_relat_1(sK0,X7)),X8),sK0)
        | r2_hidden(sK4(sK0,k10_relat_1(sK0,X7)),k10_relat_1(sK0,X7)) )
    | ~ spl10_12
    | ~ spl10_27 ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,
    ( ! [X8,X7] :
        ( k1_relat_1(sK0) = k10_relat_1(sK0,X7)
        | ~ r2_hidden(sK6(sK0,k10_relat_1(sK0,X7)),X7)
        | ~ r2_hidden(k4_tarski(sK4(sK0,k10_relat_1(sK0,X7)),X8),sK0)
        | r2_hidden(sK4(sK0,k10_relat_1(sK0,X7)),k10_relat_1(sK0,X7))
        | k1_relat_1(sK0) = k10_relat_1(sK0,X7) )
    | ~ spl10_12
    | ~ spl10_27 ),
    inference(resolution,[],[f187,f83])).

fof(f187,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(sK4(X1,k10_relat_1(sK0,X0)),X2),sK0)
        | k1_relat_1(X1) = k10_relat_1(sK0,X0)
        | ~ r2_hidden(X2,X0)
        | ~ r2_hidden(k4_tarski(sK4(X1,k10_relat_1(sK0,X0)),X3),X1) )
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f186])).

fof(f188,plain,
    ( spl10_27
    | ~ spl10_1
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f180,f169,f32,f186])).

fof(f169,plain,
    ( spl10_25
  <=> ! [X9,X11,X8,X10,X12] :
        ( ~ r2_hidden(k4_tarski(sK4(X8,k10_relat_1(X9,X10)),X11),X8)
        | k10_relat_1(X9,X10) = k1_relat_1(X8)
        | ~ r2_hidden(k4_tarski(sK4(X8,k10_relat_1(X9,X10)),X12),X9)
        | ~ r2_hidden(X12,X10)
        | ~ v1_relat_1(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f180,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_relat_1(X1) = k10_relat_1(sK0,X0)
        | ~ r2_hidden(k4_tarski(sK4(X1,k10_relat_1(sK0,X0)),X2),sK0)
        | ~ r2_hidden(X2,X0)
        | ~ r2_hidden(k4_tarski(sK4(X1,k10_relat_1(sK0,X0)),X3),X1) )
    | ~ spl10_1
    | ~ spl10_25 ),
    inference(resolution,[],[f170,f33])).

fof(f170,plain,
    ( ! [X12,X10,X8,X11,X9] :
        ( ~ v1_relat_1(X9)
        | k10_relat_1(X9,X10) = k1_relat_1(X8)
        | ~ r2_hidden(k4_tarski(sK4(X8,k10_relat_1(X9,X10)),X12),X9)
        | ~ r2_hidden(X12,X10)
        | ~ r2_hidden(k4_tarski(sK4(X8,k10_relat_1(X9,X10)),X11),X8) )
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,
    ( spl10_25
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f77,f68,f60,f169])).

fof(f60,plain,
    ( spl10_8
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f77,plain,
    ( ! [X12,X10,X8,X11,X9] :
        ( ~ r2_hidden(k4_tarski(sK4(X8,k10_relat_1(X9,X10)),X11),X8)
        | k10_relat_1(X9,X10) = k1_relat_1(X8)
        | ~ r2_hidden(k4_tarski(sK4(X8,k10_relat_1(X9,X10)),X12),X9)
        | ~ r2_hidden(X12,X10)
        | ~ v1_relat_1(X9) )
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(resolution,[],[f69,f61])).

fof(f61,plain,
    ( ! [X4,X0,X3,X1] :
        ( r2_hidden(X3,k10_relat_1(X0,X1))
        | ~ r2_hidden(k4_tarski(X3,X4),X0)
        | ~ r2_hidden(X4,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f84,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f18,f82])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f70,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f19,f68])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK2(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK2(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f62,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f24,f60])).

fof(f24,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f30,f44])).

fof(f30,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f38,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f9,f36])).

fof(f9,plain,(
    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k1_relat_1(X0) != k10_relat_1(X0,k2_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f34,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f8,f32])).

fof(f8,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
