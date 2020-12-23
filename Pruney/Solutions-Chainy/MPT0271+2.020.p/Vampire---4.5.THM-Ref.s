%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:08 EST 2020

% Result     : Theorem 27.86s
% Output     : Refutation 28.64s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 434 expanded)
%              Number of leaves         :   64 ( 187 expanded)
%              Depth                    :    9
%              Number of atoms          :  708 (1117 expanded)
%              Number of equality atoms :  106 ( 236 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58644,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f139,f151,f155,f164,f168,f172,f182,f195,f199,f221,f240,f248,f252,f264,f313,f318,f321,f362,f366,f414,f531,f577,f668,f672,f798,f826,f1158,f1281,f1517,f1909,f2226,f2460,f3111,f5239,f58561,f58643])).

fof(f58643,plain,
    ( ~ spl11_11
    | ~ spl11_22
    | spl11_31
    | ~ spl11_1130 ),
    inference(avatar_contradiction_clause,[],[f58642])).

fof(f58642,plain,
    ( $false
    | ~ spl11_11
    | ~ spl11_22
    | spl11_31
    | ~ spl11_1130 ),
    inference(subsumption_resolution,[],[f58641,f317])).

fof(f317,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | spl11_31 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl11_31
  <=> k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f58641,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ spl11_11
    | ~ spl11_22
    | ~ spl11_1130 ),
    inference(forward_demodulation,[],[f58637,f181])).

fof(f181,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl11_11
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f58637,plain,
    ( ! [X4] : k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k3_xboole_0(k1_xboole_0,X4)
    | ~ spl11_22
    | ~ spl11_1130 ),
    inference(resolution,[],[f58560,f247])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) = X2 )
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl11_22
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f58560,plain,
    ( ! [X0] : sP1(k1_xboole_0,X0,k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ spl11_1130 ),
    inference(avatar_component_clause,[],[f58559])).

fof(f58559,plain,
    ( spl11_1130
  <=> ! [X0] : sP1(k1_xboole_0,X0,k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1130])])).

fof(f58561,plain,
    ( spl11_1130
    | ~ spl11_17
    | ~ spl11_23
    | ~ spl11_145
    | ~ spl11_254 ),
    inference(avatar_split_clause,[],[f5251,f5237,f3109,f250,f219,f58559])).

fof(f219,plain,
    ( spl11_17
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f250,plain,
    ( spl11_23
  <=> ! [X1,X0] : ~ sP0(X0,X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f3109,plain,
    ( spl11_145
  <=> ! [X1,X3,X0,X2] :
        ( sP0(X0,sK9(X1,X0,X2),X1)
        | sP1(X1,X0,X2)
        | r2_hidden(sK9(X1,X0,X2),X3)
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_145])])).

fof(f5237,plain,
    ( spl11_254
  <=> r1_tarski(k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_254])])).

fof(f5251,plain,
    ( ! [X0] : sP1(k1_xboole_0,X0,k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ spl11_17
    | ~ spl11_23
    | ~ spl11_145
    | ~ spl11_254 ),
    inference(unit_resulting_resolution,[],[f220,f251,f5238,f3110])).

fof(f3110,plain,
    ( ! [X2,X0,X3,X1] :
        ( sP0(X0,sK9(X1,X0,X2),X1)
        | r2_hidden(sK9(X1,X0,X2),X3)
        | sP1(X1,X0,X2)
        | ~ r1_tarski(X2,X3) )
    | ~ spl11_145 ),
    inference(avatar_component_clause,[],[f3109])).

fof(f5238,plain,
    ( r1_tarski(k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k1_xboole_0)
    | ~ spl11_254 ),
    inference(avatar_component_clause,[],[f5237])).

fof(f251,plain,
    ( ! [X0,X1] : ~ sP0(X0,X1,k1_xboole_0)
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f250])).

fof(f220,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f219])).

fof(f5239,plain,
    ( spl11_254
    | ~ spl11_8
    | ~ spl11_88
    | ~ spl11_103 ),
    inference(avatar_split_clause,[],[f2677,f2458,f1515,f162,f5237])).

fof(f162,plain,
    ( spl11_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f1515,plain,
    ( spl11_88
  <=> r1_tarski(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f2458,plain,
    ( spl11_103
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,X0)
        | r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).

fof(f2677,plain,
    ( r1_tarski(k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k1_xboole_0)
    | ~ spl11_8
    | ~ spl11_88
    | ~ spl11_103 ),
    inference(forward_demodulation,[],[f2672,f163])).

fof(f163,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f2672,plain,
    ( r1_tarski(k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)),k1_xboole_0)
    | ~ spl11_88
    | ~ spl11_103 ),
    inference(unit_resulting_resolution,[],[f1516,f2459])).

fof(f2459,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0)
        | ~ r1_tarski(X1,X0) )
    | ~ spl11_103 ),
    inference(avatar_component_clause,[],[f2458])).

fof(f1516,plain,
    ( r1_tarski(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)
    | ~ spl11_88 ),
    inference(avatar_component_clause,[],[f1515])).

fof(f3111,plain,
    ( spl11_145
    | ~ spl11_20
    | ~ spl11_79 ),
    inference(avatar_split_clause,[],[f1216,f1156,f238,f3109])).

fof(f238,plain,
    ( spl11_20
  <=> ! [X1,X3,X0] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f1156,plain,
    ( spl11_79
  <=> ! [X1,X0,X2] :
        ( sP1(X0,X1,X2)
        | sP0(X1,sK9(X0,X1,X2),X0)
        | r2_hidden(sK9(X0,X1,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_79])])).

fof(f1216,plain,
    ( ! [X2,X0,X3,X1] :
        ( sP0(X0,sK9(X1,X0,X2),X1)
        | sP1(X1,X0,X2)
        | r2_hidden(sK9(X1,X0,X2),X3)
        | ~ r1_tarski(X2,X3) )
    | ~ spl11_20
    | ~ spl11_79 ),
    inference(resolution,[],[f1157,f239])).

fof(f239,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X0)
        | r2_hidden(X3,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f238])).

fof(f1157,plain,
    ( ! [X2,X0,X1] :
        ( sP0(X1,sK9(X0,X1,X2),X0)
        | r2_hidden(sK9(X0,X1,X2),X2)
        | sP1(X0,X1,X2) )
    | ~ spl11_79 ),
    inference(avatar_component_clause,[],[f1156])).

fof(f2460,plain,
    ( spl11_103
    | ~ spl11_56
    | ~ spl11_82 ),
    inference(avatar_split_clause,[],[f1331,f1279,f575,f2458])).

fof(f575,plain,
    ( spl11_56
  <=> ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f1279,plain,
    ( spl11_82
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
        | ~ r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).

fof(f1331,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0) )
    | ~ spl11_56
    | ~ spl11_82 ),
    inference(superposition,[],[f1280,f576])).

fof(f576,plain,
    ( ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f575])).

fof(f1280,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
        | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) )
    | ~ spl11_82 ),
    inference(avatar_component_clause,[],[f1279])).

fof(f2226,plain,
    ( ~ spl11_5
    | ~ spl11_43
    | ~ spl11_60
    | ~ spl11_61
    | ~ spl11_63
    | ~ spl11_95 ),
    inference(avatar_contradiction_clause,[],[f2225])).

fof(f2225,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_43
    | ~ spl11_60
    | ~ spl11_61
    | ~ spl11_63
    | ~ spl11_95 ),
    inference(subsumption_resolution,[],[f2214,f881])).

fof(f881,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
    | ~ spl11_5
    | ~ spl11_60
    | ~ spl11_63 ),
    inference(unit_resulting_resolution,[],[f150,f667,f797])).

fof(f797,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( ~ sP4(X0,X1,X2,X3)
        | ~ sP3(X5,X2,X1,X0)
        | r2_hidden(X5,X3) )
    | ~ spl11_63 ),
    inference(avatar_component_clause,[],[f796])).

fof(f796,plain,
    ( spl11_63
  <=> ! [X1,X3,X5,X0,X2] :
        ( r2_hidden(X5,X3)
        | ~ sP3(X5,X2,X1,X0)
        | ~ sP4(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).

fof(f667,plain,
    ( ! [X2,X0,X1] : sP4(X0,X1,X2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
    | ~ spl11_60 ),
    inference(avatar_component_clause,[],[f666])).

fof(f666,plain,
    ( spl11_60
  <=> ! [X1,X0,X2] : sP4(X0,X1,X2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f150,plain,
    ( ! [X2,X3,X1] : sP3(X3,X1,X2,X3)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl11_5
  <=> ! [X1,X3,X2] : sP3(X3,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f2214,plain,
    ( ~ r2_hidden(sK5,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ spl11_43
    | ~ spl11_61
    | ~ spl11_95 ),
    inference(unit_resulting_resolution,[],[f1908,f671,f413])).

fof(f413,plain,
    ( ! [X2,X0,X1] :
        ( sP2(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
    | ~ spl11_43 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl11_43
  <=> ! [X1,X0,X2] :
        ( sP2(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f671,plain,
    ( ! [X0] : ~ r2_hidden(sK5,k3_xboole_0(sK6,X0))
    | ~ spl11_61 ),
    inference(avatar_component_clause,[],[f670])).

fof(f670,plain,
    ( spl11_61
  <=> ! [X0] : ~ r2_hidden(sK5,k3_xboole_0(sK6,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f1908,plain,
    ( ! [X0] : ~ sP2(k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ spl11_95 ),
    inference(avatar_component_clause,[],[f1907])).

fof(f1907,plain,
    ( spl11_95
  <=> ! [X0] : ~ sP2(k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_95])])).

fof(f1909,plain,
    ( spl11_95
    | ~ spl11_17
    | ~ spl11_26
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f1795,f316,f262,f219,f1907])).

fof(f262,plain,
    ( spl11_26
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f1795,plain,
    ( ! [X0] : ~ sP2(k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ spl11_17
    | ~ spl11_26
    | ~ spl11_31 ),
    inference(subsumption_resolution,[],[f1793,f220])).

fof(f1793,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ sP2(k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) )
    | ~ spl11_26
    | ~ spl11_31 ),
    inference(superposition,[],[f263,f361])).

fof(f361,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f316])).

fof(f263,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP2(X2,X0,X1) )
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f262])).

fof(f1517,plain,
    ( spl11_88
    | ~ spl11_30
    | ~ spl11_65 ),
    inference(avatar_split_clause,[],[f1415,f824,f311,f1515])).

fof(f311,plain,
    ( spl11_30
  <=> r2_hidden(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f824,plain,
    ( spl11_65
  <=> ! [X1,X0] :
        ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).

fof(f1415,plain,
    ( r1_tarski(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)
    | ~ spl11_30
    | ~ spl11_65 ),
    inference(unit_resulting_resolution,[],[f320,f825])).

fof(f825,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl11_65 ),
    inference(avatar_component_clause,[],[f824])).

fof(f320,plain,
    ( r2_hidden(sK5,sK6)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f311])).

fof(f1281,plain,(
    spl11_82 ),
    inference(avatar_split_clause,[],[f124,f1279])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
      | ~ r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f84,f75,f117])).

fof(f117,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f116])).

fof(f116,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f83,f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f100,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f111,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f111,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f73,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1158,plain,(
    spl11_79 ),
    inference(avatar_split_clause,[],[f87,f1156])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | sP0(X1,sK9(X0,X1,X2),X0)
      | r2_hidden(sK9(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sP0(X1,sK9(X0,X1,X2),X0)
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sP0(X1,sK9(X0,X1,X2),X0)
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f826,plain,(
    spl11_65 ),
    inference(avatar_split_clause,[],[f122,f824])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f82,f118])).

fof(f118,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f116])).

fof(f71,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f798,plain,(
    spl11_63 ),
    inference(avatar_split_clause,[],[f102,f796])).

fof(f102,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP3(X5,X2,X1,X0)
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ( ( ~ sP3(sK10(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK10(X0,X1,X2,X3),X3) )
          & ( sP3(sK10(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK10(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f59,f60])).

fof(f60,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP3(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP3(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP3(sK10(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK10(X0,X1,X2,X3),X3) )
        & ( sP3(sK10(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK10(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP3(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP3(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP3(X4,X2,X1,X0) )
            & ( sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( sP4(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP3(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f672,plain,
    ( spl11_61
    | ~ spl11_13
    | ~ spl11_38
    | ~ spl11_52 ),
    inference(avatar_split_clause,[],[f593,f529,f364,f193,f670])).

fof(f193,plain,
    ( spl11_13
  <=> ! [X1,X2] : sP1(X1,X2,k3_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f364,plain,
    ( spl11_38
  <=> ! [X0] : ~ sP0(sK6,sK5,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f529,plain,
    ( spl11_52
  <=> ! [X1,X0,X2,X4] :
        ( sP0(X1,X4,X0)
        | ~ r2_hidden(X4,X2)
        | ~ sP1(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f593,plain,
    ( ! [X0] : ~ r2_hidden(sK5,k3_xboole_0(sK6,X0))
    | ~ spl11_13
    | ~ spl11_38
    | ~ spl11_52 ),
    inference(unit_resulting_resolution,[],[f365,f194,f530])).

fof(f530,plain,
    ( ! [X4,X2,X0,X1] :
        ( ~ sP1(X0,X1,X2)
        | ~ r2_hidden(X4,X2)
        | sP0(X1,X4,X0) )
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f529])).

fof(f194,plain,
    ( ! [X2,X1] : sP1(X1,X2,k3_xboole_0(X2,X1))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f193])).

fof(f365,plain,
    ( ! [X0] : ~ sP0(sK6,sK5,X0)
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f364])).

fof(f668,plain,(
    spl11_60 ),
    inference(avatar_split_clause,[],[f131,f666])).

fof(f131,plain,(
    ! [X2,X0,X1] : sP4(X0,X1,X2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f109,f115])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP4(X0,X1,X2,X3) )
      & ( sP4(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP4(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f28,f35,f34])).

fof(f34,plain,(
    ! [X4,X2,X1,X0] :
      ( sP3(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f577,plain,(
    spl11_56 ),
    inference(avatar_split_clause,[],[f121,f575])).

fof(f121,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f70,f117])).

fof(f70,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f531,plain,(
    spl11_52 ),
    inference(avatar_split_clause,[],[f85,f529])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X1,X4,X0)
      | ~ r2_hidden(X4,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f414,plain,(
    spl11_43 ),
    inference(avatar_split_clause,[],[f96,f412])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f366,plain,
    ( spl11_38
    | ~ spl11_10
    | spl11_30 ),
    inference(avatar_split_clause,[],[f359,f311,f170,f364])).

fof(f170,plain,
    ( spl11_10
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X1,X0)
        | ~ sP0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f359,plain,
    ( ! [X0] : ~ sP0(sK6,sK5,X0)
    | ~ spl11_10
    | spl11_30 ),
    inference(unit_resulting_resolution,[],[f312,f171])).

fof(f171,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(X0,X1,X2)
        | r2_hidden(X1,X0) )
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f312,plain,
    ( ~ r2_hidden(sK5,sK6)
    | spl11_30 ),
    inference(avatar_component_clause,[],[f311])).

fof(f362,plain,
    ( spl11_31
    | ~ spl11_8
    | ~ spl11_29 ),
    inference(avatar_split_clause,[],[f354,f308,f162,f316])).

fof(f308,plain,
    ( spl11_29
  <=> k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f354,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ spl11_8
    | ~ spl11_29 ),
    inference(forward_demodulation,[],[f319,f163])).

fof(f319,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f308])).

fof(f321,plain,
    ( spl11_29
    | spl11_30 ),
    inference(avatar_split_clause,[],[f120,f311,f308])).

fof(f120,plain,
    ( r2_hidden(sK5,sK6)
    | k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)) ),
    inference(definition_unfolding,[],[f66,f75,f118])).

fof(f66,plain,
    ( r2_hidden(sK5,sK6)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r2_hidden(sK5,sK6)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6) )
    & ( r2_hidden(sK5,sK6)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f37,f38])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK5,sK6)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6) )
      & ( r2_hidden(sK5,sK6)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f318,plain,
    ( ~ spl11_31
    | ~ spl11_8
    | spl11_29 ),
    inference(avatar_split_clause,[],[f314,f308,f162,f316])).

fof(f314,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ spl11_8
    | spl11_29 ),
    inference(forward_demodulation,[],[f309,f163])).

fof(f309,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))
    | spl11_29 ),
    inference(avatar_component_clause,[],[f308])).

fof(f313,plain,
    ( ~ spl11_29
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f119,f311,f308])).

fof(f119,plain,
    ( ~ r2_hidden(sK5,sK6)
    | k1_xboole_0 != k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)) ),
    inference(definition_unfolding,[],[f67,f75,f118])).

fof(f67,plain,
    ( ~ r2_hidden(sK5,sK6)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f264,plain,(
    spl11_26 ),
    inference(avatar_split_clause,[],[f99,f262])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP2(X2,X0,X1) )
      & ( sP2(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP2(X2,X0,X1) ) ),
    inference(definition_folding,[],[f27,f32])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f252,plain,
    ( spl11_23
    | ~ spl11_9
    | ~ spl11_17 ),
    inference(avatar_split_clause,[],[f224,f219,f166,f250])).

fof(f166,plain,
    ( spl11_9
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f224,plain,
    ( ! [X0,X1] : ~ sP0(X0,X1,k1_xboole_0)
    | ~ spl11_9
    | ~ spl11_17 ),
    inference(unit_resulting_resolution,[],[f220,f167])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(X0,X1,X2)
        | r2_hidden(X1,X2) )
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f166])).

fof(f248,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f93,f246])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f30,f29])).

fof(f29,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f240,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f78,f238])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f221,plain,
    ( spl11_17
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f217,f197,f137,f133,f219])).

fof(f133,plain,
    ( spl11_1
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f137,plain,
    ( spl11_2
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f197,plain,
    ( spl11_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f217,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_14 ),
    inference(forward_demodulation,[],[f212,f138])).

fof(f138,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f137])).

fof(f212,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))
    | ~ spl11_1
    | ~ spl11_14 ),
    inference(unit_resulting_resolution,[],[f134,f198])).

fof(f198,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f134,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f133])).

fof(f199,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f77,f197])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f195,plain,
    ( spl11_13
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f176,f162,f153,f193])).

fof(f153,plain,
    ( spl11_6
  <=> ! [X1,X0] : sP1(X0,X1,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f176,plain,
    ( ! [X2,X1] : sP1(X1,X2,k3_xboole_0(X2,X1))
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(superposition,[],[f154,f163])).

fof(f154,plain,
    ( ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X0,X1))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f182,plain,
    ( spl11_11
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f173,f162,f137,f180])).

fof(f173,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(superposition,[],[f163,f138])).

fof(f172,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f90,f170])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f168,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f89,f166])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f164,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f72,f162])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f155,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f127,f153])).

fof(f127,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f151,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f130,f149])).

fof(f130,plain,(
    ! [X2,X3,X1] : sP3(X3,X1,X2,X3) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f139,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f69,f137])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f135,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f68,f133])).

fof(f68,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (11703)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (11692)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (11713)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (11705)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % (11702)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.55  % (11697)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.55  % (11699)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.55  % (11702)Refutation not found, incomplete strategy% (11702)------------------------------
% 1.36/0.55  % (11702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (11702)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (11702)Memory used [KB]: 10618
% 1.36/0.55  % (11702)Time elapsed: 0.134 s
% 1.36/0.55  % (11702)------------------------------
% 1.36/0.55  % (11702)------------------------------
% 1.36/0.55  % (11695)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.56  % (11720)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.56  % (11694)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.56  % (11712)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.53/0.56  % (11707)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.56  % (11696)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.57  % (11710)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.57  % (11709)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.57  % (11691)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.53/0.57  % (11717)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.53/0.57  % (11718)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.57  % (11715)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.57  % (11693)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.57  % (11719)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.58  % (11711)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.53/0.58  % (11701)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.53/0.58  % (11701)Refutation not found, incomplete strategy% (11701)------------------------------
% 1.53/0.58  % (11701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (11701)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (11701)Memory used [KB]: 10618
% 1.53/0.58  % (11701)Time elapsed: 0.171 s
% 1.53/0.58  % (11701)------------------------------
% 1.53/0.58  % (11701)------------------------------
% 1.53/0.58  % (11698)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.59  % (11704)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.59  % (11711)Refutation not found, incomplete strategy% (11711)------------------------------
% 1.53/0.59  % (11711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (11706)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.53/0.61  % (11711)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.61  
% 1.53/0.61  % (11711)Memory used [KB]: 10746
% 1.53/0.61  % (11711)Time elapsed: 0.159 s
% 1.53/0.61  % (11711)------------------------------
% 1.53/0.61  % (11711)------------------------------
% 1.53/0.61  % (11714)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.62  % (11716)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.63  % (11708)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.64  % (11700)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.85/0.76  % (11745)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.85/0.81  % (11747)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.28/0.82  % (11746)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.28/0.84  % (11696)Time limit reached!
% 3.28/0.84  % (11696)------------------------------
% 3.28/0.84  % (11696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.28/0.84  % (11696)Termination reason: Time limit
% 3.28/0.84  % (11696)Termination phase: Saturation
% 3.28/0.84  
% 3.28/0.84  % (11696)Memory used [KB]: 8315
% 3.28/0.84  % (11696)Time elapsed: 0.400 s
% 3.28/0.84  % (11696)------------------------------
% 3.28/0.84  % (11696)------------------------------
% 3.70/0.92  % (11703)Time limit reached!
% 3.70/0.92  % (11703)------------------------------
% 3.70/0.92  % (11703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.92  % (11703)Termination reason: Time limit
% 3.70/0.92  
% 3.70/0.92  % (11703)Memory used [KB]: 7803
% 3.70/0.92  % (11703)Time elapsed: 0.513 s
% 3.70/0.92  % (11703)------------------------------
% 3.70/0.92  % (11703)------------------------------
% 3.70/0.94  % (11708)Time limit reached!
% 3.70/0.94  % (11708)------------------------------
% 3.70/0.94  % (11708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.94  % (11691)Time limit reached!
% 3.70/0.94  % (11691)------------------------------
% 3.70/0.94  % (11691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.95  % (11708)Termination reason: Time limit
% 3.70/0.95  % (11708)Termination phase: Saturation
% 3.70/0.95  
% 3.70/0.95  % (11708)Memory used [KB]: 12537
% 3.70/0.95  % (11708)Time elapsed: 0.500 s
% 3.70/0.95  % (11708)------------------------------
% 3.70/0.95  % (11708)------------------------------
% 3.70/0.95  % (11691)Termination reason: Time limit
% 3.70/0.95  
% 3.70/0.95  % (11691)Memory used [KB]: 2430
% 3.70/0.95  % (11691)Time elapsed: 0.510 s
% 3.70/0.95  % (11691)------------------------------
% 3.70/0.95  % (11691)------------------------------
% 4.32/0.96  % (11692)Time limit reached!
% 4.32/0.96  % (11692)------------------------------
% 4.32/0.96  % (11692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/0.98  % (11692)Termination reason: Time limit
% 4.32/0.98  
% 4.32/0.98  % (11692)Memory used [KB]: 9466
% 4.32/0.98  % (11692)Time elapsed: 0.514 s
% 4.32/0.98  % (11692)------------------------------
% 4.32/0.98  % (11692)------------------------------
% 4.32/0.98  % (11748)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.53/1.03  % (11707)Time limit reached!
% 4.53/1.03  % (11707)------------------------------
% 4.53/1.03  % (11707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/1.03  % (11707)Termination reason: Time limit
% 4.53/1.03  
% 4.53/1.03  % (11707)Memory used [KB]: 14967
% 4.53/1.03  % (11707)Time elapsed: 0.615 s
% 4.53/1.03  % (11707)------------------------------
% 4.53/1.03  % (11707)------------------------------
% 4.81/1.05  % (11698)Time limit reached!
% 4.81/1.05  % (11698)------------------------------
% 4.81/1.05  % (11698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.05  % (11698)Termination reason: Time limit
% 4.81/1.05  % (11698)Termination phase: Saturation
% 4.81/1.05  
% 4.81/1.05  % (11698)Memory used [KB]: 9594
% 4.81/1.05  % (11698)Time elapsed: 0.600 s
% 4.81/1.05  % (11698)------------------------------
% 4.81/1.05  % (11698)------------------------------
% 4.81/1.05  % (11719)Time limit reached!
% 4.81/1.05  % (11719)------------------------------
% 4.81/1.05  % (11719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.05  % (11719)Termination reason: Time limit
% 4.81/1.05  
% 4.81/1.05  % (11719)Memory used [KB]: 8827
% 4.81/1.05  % (11719)Time elapsed: 0.630 s
% 4.81/1.05  % (11719)------------------------------
% 4.81/1.05  % (11719)------------------------------
% 5.46/1.10  % (11749)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.46/1.10  % (11751)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.98/1.14  % (11750)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.38/1.20  % (11752)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.38/1.22  % (11754)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.38/1.24  % (11712)Time limit reached!
% 6.38/1.24  % (11712)------------------------------
% 6.38/1.24  % (11712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.38/1.24  % (11712)Termination reason: Time limit
% 6.38/1.24  % (11712)Termination phase: Saturation
% 6.38/1.24  
% 6.38/1.24  % (11712)Memory used [KB]: 3070
% 6.38/1.24  % (11712)Time elapsed: 0.800 s
% 6.38/1.24  % (11712)------------------------------
% 6.38/1.24  % (11712)------------------------------
% 6.38/1.24  % (11753)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.38/1.24  % (11753)Refutation not found, incomplete strategy% (11753)------------------------------
% 6.38/1.24  % (11753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.38/1.24  % (11753)Termination reason: Refutation not found, incomplete strategy
% 6.38/1.24  
% 6.38/1.24  % (11753)Memory used [KB]: 1791
% 6.38/1.24  % (11753)Time elapsed: 0.180 s
% 6.38/1.24  % (11753)------------------------------
% 6.38/1.24  % (11753)------------------------------
% 6.97/1.28  % (11755)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.50/1.35  % (11748)Time limit reached!
% 7.50/1.35  % (11748)------------------------------
% 7.50/1.35  % (11748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.50/1.35  % (11748)Termination reason: Time limit
% 7.50/1.35  % (11748)Termination phase: Saturation
% 7.50/1.35  
% 7.50/1.35  % (11748)Memory used [KB]: 7931
% 7.50/1.35  % (11748)Time elapsed: 0.400 s
% 7.50/1.35  % (11748)------------------------------
% 7.50/1.35  % (11748)------------------------------
% 7.50/1.40  % (11749)Time limit reached!
% 7.50/1.40  % (11749)------------------------------
% 7.50/1.40  % (11749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.50/1.40  % (11749)Termination reason: Time limit
% 7.50/1.40  
% 7.50/1.40  % (11749)Memory used [KB]: 12920
% 7.50/1.40  % (11749)Time elapsed: 0.430 s
% 7.50/1.40  % (11749)------------------------------
% 7.50/1.40  % (11749)------------------------------
% 7.50/1.42  % (11757)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.09/1.44  % (11693)Time limit reached!
% 8.09/1.44  % (11693)------------------------------
% 8.09/1.44  % (11693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.09/1.44  % (11693)Termination reason: Time limit
% 8.09/1.44  
% 8.09/1.44  % (11693)Memory used [KB]: 11513
% 8.09/1.44  % (11693)Time elapsed: 1.002 s
% 8.09/1.44  % (11693)------------------------------
% 8.09/1.44  % (11693)------------------------------
% 8.09/1.47  % (11756)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.46/1.51  % (11758)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 8.46/1.51  % (11758)Refutation not found, incomplete strategy% (11758)------------------------------
% 8.46/1.51  % (11758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.46/1.51  % (11758)Termination reason: Refutation not found, incomplete strategy
% 8.46/1.51  
% 8.46/1.51  % (11758)Memory used [KB]: 1791
% 8.46/1.51  % (11758)Time elapsed: 0.114 s
% 8.46/1.51  % (11758)------------------------------
% 8.46/1.51  % (11758)------------------------------
% 8.96/1.61  % (11717)Time limit reached!
% 8.96/1.61  % (11717)------------------------------
% 8.96/1.61  % (11717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.96/1.61  % (11717)Termination reason: Time limit
% 8.96/1.61  % (11717)Termination phase: Saturation
% 8.96/1.61  
% 8.96/1.61  % (11717)Memory used [KB]: 20084
% 8.96/1.61  % (11717)Time elapsed: 1.200 s
% 8.96/1.61  % (11717)------------------------------
% 8.96/1.61  % (11717)------------------------------
% 8.96/1.64  % (11760)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 8.96/1.65  % (11759)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.96/1.67  % (11761)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 10.42/1.71  % (11713)Time limit reached!
% 10.42/1.71  % (11713)------------------------------
% 10.42/1.71  % (11713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.71  % (11713)Termination reason: Time limit
% 10.42/1.71  
% 10.42/1.71  % (11713)Memory used [KB]: 16502
% 10.42/1.71  % (11713)Time elapsed: 1.297 s
% 10.42/1.71  % (11713)------------------------------
% 10.42/1.71  % (11713)------------------------------
% 10.42/1.75  % (11706)Time limit reached!
% 10.42/1.75  % (11706)------------------------------
% 10.42/1.75  % (11706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.75  % (11706)Termination reason: Time limit
% 10.42/1.75  % (11706)Termination phase: Saturation
% 10.42/1.75  
% 10.42/1.75  % (11706)Memory used [KB]: 12792
% 10.42/1.75  % (11706)Time elapsed: 1.300 s
% 10.42/1.75  % (11706)------------------------------
% 10.42/1.75  % (11706)------------------------------
% 11.12/1.78  % (11715)Time limit reached!
% 11.12/1.78  % (11715)------------------------------
% 11.12/1.78  % (11715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.12/1.78  % (11715)Termination reason: Time limit
% 11.12/1.78  
% 11.12/1.78  % (11715)Memory used [KB]: 17782
% 11.12/1.78  % (11715)Time elapsed: 1.345 s
% 11.12/1.78  % (11715)------------------------------
% 11.12/1.78  % (11715)------------------------------
% 11.12/1.78  % (11757)Time limit reached!
% 11.12/1.78  % (11757)------------------------------
% 11.12/1.78  % (11757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.12/1.78  % (11757)Termination reason: Time limit
% 11.12/1.78  % (11757)Termination phase: Saturation
% 11.12/1.78  
% 11.12/1.78  % (11757)Memory used [KB]: 2942
% 11.12/1.78  % (11757)Time elapsed: 0.500 s
% 11.12/1.78  % (11757)------------------------------
% 11.12/1.78  % (11757)------------------------------
% 11.17/1.79  % (11762)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.43/1.91  % (11718)Time limit reached!
% 11.43/1.91  % (11718)------------------------------
% 11.43/1.91  % (11718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.43/1.91  % (11718)Termination reason: Time limit
% 11.43/1.91  
% 11.43/1.91  % (11718)Memory used [KB]: 10234
% 11.43/1.91  % (11718)Time elapsed: 1.501 s
% 11.43/1.91  % (11718)------------------------------
% 11.43/1.91  % (11718)------------------------------
% 12.07/1.94  % (11763)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.07/1.94  % (11766)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 12.07/1.96  % (11764)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 12.07/1.96  % (11761)Time limit reached!
% 12.07/1.96  % (11761)------------------------------
% 12.07/1.96  % (11761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.07/1.96  % (11761)Termination reason: Time limit
% 12.07/1.96  
% 12.07/1.96  % (11761)Memory used [KB]: 4093
% 12.07/1.96  % (11761)Time elapsed: 0.407 s
% 12.07/1.96  % (11761)------------------------------
% 12.07/1.96  % (11761)------------------------------
% 12.58/2.00  % (11765)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 12.58/2.05  % (11695)Time limit reached!
% 12.58/2.05  % (11695)------------------------------
% 12.58/2.05  % (11695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.58/2.05  % (11695)Termination reason: Time limit
% 12.58/2.05  
% 12.58/2.05  % (11695)Memory used [KB]: 15223
% 12.58/2.05  % (11695)Time elapsed: 1.626 s
% 12.58/2.05  % (11695)------------------------------
% 12.58/2.05  % (11695)------------------------------
% 13.27/2.12  % (11768)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 14.03/2.16  % (11767)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 14.03/2.21  % (11769)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 14.03/2.21  % (11764)Time limit reached!
% 14.03/2.21  % (11764)------------------------------
% 14.03/2.21  % (11764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.03/2.21  % (11764)Termination reason: Time limit
% 14.03/2.21  
% 14.03/2.21  % (11764)Memory used [KB]: 2686
% 14.03/2.21  % (11764)Time elapsed: 0.421 s
% 14.03/2.21  % (11764)------------------------------
% 14.03/2.21  % (11764)------------------------------
% 15.48/2.37  % (11747)Time limit reached!
% 15.48/2.37  % (11747)------------------------------
% 15.48/2.37  % (11747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.48/2.37  % (11747)Termination reason: Time limit
% 15.48/2.37  % (11747)Termination phase: Saturation
% 15.48/2.37  
% 15.48/2.37  % (11747)Memory used [KB]: 14583
% 15.48/2.37  % (11747)Time elapsed: 1.700 s
% 15.48/2.37  % (11747)------------------------------
% 15.48/2.37  % (11747)------------------------------
% 15.48/2.37  % (11705)Time limit reached!
% 15.48/2.37  % (11705)------------------------------
% 15.48/2.37  % (11705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.48/2.37  % (11705)Termination reason: Time limit
% 15.48/2.37  
% 15.48/2.37  % (11705)Memory used [KB]: 6012
% 15.48/2.37  % (11705)Time elapsed: 1.843 s
% 15.48/2.37  % (11705)------------------------------
% 15.48/2.37  % (11705)------------------------------
% 15.91/2.43  % (11770)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 15.91/2.43  % (11770)Refutation not found, incomplete strategy% (11770)------------------------------
% 15.91/2.43  % (11770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.91/2.43  % (11770)Termination reason: Refutation not found, incomplete strategy
% 15.91/2.43  
% 15.91/2.43  % (11770)Memory used [KB]: 6268
% 15.91/2.43  % (11770)Time elapsed: 0.188 s
% 15.91/2.43  % (11770)------------------------------
% 15.91/2.43  % (11770)------------------------------
% 15.91/2.45  % (11709)Time limit reached!
% 15.91/2.45  % (11709)------------------------------
% 15.91/2.45  % (11709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.91/2.45  % (11709)Termination reason: Time limit
% 15.91/2.45  % (11709)Termination phase: Saturation
% 15.91/2.45  
% 15.91/2.45  % (11709)Memory used [KB]: 19829
% 15.91/2.45  % (11709)Time elapsed: 2.0000 s
% 15.91/2.45  % (11709)------------------------------
% 15.91/2.45  % (11709)------------------------------
% 16.98/2.52  % (11769)Time limit reached!
% 16.98/2.52  % (11769)------------------------------
% 16.98/2.52  % (11769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.98/2.52  % (11769)Termination reason: Time limit
% 16.98/2.52  
% 16.98/2.52  % (11769)Memory used [KB]: 9338
% 16.98/2.52  % (11769)Time elapsed: 0.419 s
% 16.98/2.52  % (11769)------------------------------
% 16.98/2.52  % (11769)------------------------------
% 16.98/2.53  % (11697)Time limit reached!
% 16.98/2.53  % (11697)------------------------------
% 16.98/2.53  % (11697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.98/2.53  % (11697)Termination reason: Time limit
% 16.98/2.53  
% 16.98/2.53  % (11697)Memory used [KB]: 18038
% 16.98/2.53  % (11697)Time elapsed: 2.015 s
% 16.98/2.53  % (11697)------------------------------
% 16.98/2.53  % (11697)------------------------------
% 17.18/2.55  % (11751)Time limit reached!
% 17.18/2.55  % (11751)------------------------------
% 17.18/2.55  % (11751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.18/2.55  % (11751)Termination reason: Time limit
% 17.18/2.55  % (11751)Termination phase: Saturation
% 17.18/2.55  
% 17.18/2.55  % (11751)Memory used [KB]: 13816
% 17.18/2.55  % (11751)Time elapsed: 1.200 s
% 17.18/2.55  % (11751)------------------------------
% 17.18/2.55  % (11751)------------------------------
% 17.18/2.56  % (11772)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 17.18/2.57  % (11772)Refutation not found, incomplete strategy% (11772)------------------------------
% 17.18/2.57  % (11772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.18/2.57  % (11772)Termination reason: Refutation not found, incomplete strategy
% 17.18/2.57  
% 17.18/2.57  % (11772)Memory used [KB]: 10746
% 17.18/2.57  % (11772)Time elapsed: 0.149 s
% 17.18/2.57  % (11772)------------------------------
% 17.18/2.57  % (11772)------------------------------
% 17.18/2.59  % (11771)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.18/2.59  % (11771)Refutation not found, incomplete strategy% (11771)------------------------------
% 17.18/2.59  % (11771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.18/2.59  % (11771)Termination reason: Refutation not found, incomplete strategy
% 17.18/2.59  
% 17.18/2.59  % (11771)Memory used [KB]: 6268
% 17.18/2.59  % (11771)Time elapsed: 0.181 s
% 17.18/2.59  % (11771)------------------------------
% 17.18/2.59  % (11771)------------------------------
% 18.36/2.68  % (11760)Time limit reached!
% 18.36/2.68  % (11760)------------------------------
% 18.36/2.68  % (11760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.36/2.68  % (11760)Termination reason: Time limit
% 18.36/2.68  % (11760)Termination phase: Saturation
% 18.36/2.68  
% 18.36/2.68  % (11760)Memory used [KB]: 11257
% 18.36/2.68  % (11760)Time elapsed: 1.200 s
% 18.36/2.68  % (11760)------------------------------
% 18.36/2.68  % (11760)------------------------------
% 20.56/2.96  % (11699)Time limit reached!
% 20.56/2.96  % (11699)------------------------------
% 20.56/2.96  % (11699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.56/2.96  % (11699)Termination reason: Time limit
% 20.56/2.96  
% 20.56/2.96  % (11699)Memory used [KB]: 12281
% 20.56/2.96  % (11699)Time elapsed: 2.523 s
% 20.56/2.96  % (11699)------------------------------
% 20.56/2.96  % (11699)------------------------------
% 21.17/3.03  % (11710)Time limit reached!
% 21.17/3.03  % (11710)------------------------------
% 21.17/3.03  % (11710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.17/3.03  % (11710)Termination reason: Time limit
% 21.17/3.03  
% 21.17/3.03  % (11710)Memory used [KB]: 24946
% 21.17/3.03  % (11710)Time elapsed: 2.605 s
% 21.17/3.03  % (11710)------------------------------
% 21.17/3.03  % (11710)------------------------------
% 21.53/3.09  % (11763)Time limit reached!
% 21.53/3.09  % (11763)------------------------------
% 21.53/3.09  % (11763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.53/3.09  % (11763)Termination reason: Time limit
% 21.53/3.09  
% 21.53/3.09  % (11763)Memory used [KB]: 14200
% 21.53/3.09  % (11763)Time elapsed: 1.335 s
% 21.53/3.09  % (11763)------------------------------
% 21.53/3.09  % (11763)------------------------------
% 24.13/3.43  % (11704)Time limit reached!
% 24.13/3.43  % (11704)------------------------------
% 24.13/3.43  % (11704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.13/3.43  % (11704)Termination reason: Time limit
% 24.13/3.43  % (11704)Termination phase: Saturation
% 24.13/3.43  
% 24.13/3.43  % (11704)Memory used [KB]: 20852
% 24.13/3.43  % (11704)Time elapsed: 3.0000 s
% 24.13/3.43  % (11704)------------------------------
% 24.13/3.43  % (11704)------------------------------
% 24.69/3.48  % (11746)Time limit reached!
% 24.69/3.48  % (11746)------------------------------
% 24.69/3.48  % (11746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.69/3.48  % (11746)Termination reason: Time limit
% 24.69/3.48  
% 24.69/3.48  % (11746)Memory used [KB]: 15991
% 24.69/3.48  % (11746)Time elapsed: 2.827 s
% 24.69/3.48  % (11746)------------------------------
% 24.69/3.48  % (11746)------------------------------
% 27.86/3.96  % (11759)Refutation found. Thanks to Tanya!
% 27.86/3.96  % SZS status Theorem for theBenchmark
% 27.86/3.96  % SZS output start Proof for theBenchmark
% 27.86/3.96  fof(f58644,plain,(
% 27.86/3.96    $false),
% 27.86/3.96    inference(avatar_sat_refutation,[],[f135,f139,f151,f155,f164,f168,f172,f182,f195,f199,f221,f240,f248,f252,f264,f313,f318,f321,f362,f366,f414,f531,f577,f668,f672,f798,f826,f1158,f1281,f1517,f1909,f2226,f2460,f3111,f5239,f58561,f58643])).
% 27.86/3.96  fof(f58643,plain,(
% 27.86/3.96    ~spl11_11 | ~spl11_22 | spl11_31 | ~spl11_1130),
% 27.86/3.96    inference(avatar_contradiction_clause,[],[f58642])).
% 27.86/3.96  fof(f58642,plain,(
% 27.86/3.96    $false | (~spl11_11 | ~spl11_22 | spl11_31 | ~spl11_1130)),
% 27.86/3.96    inference(subsumption_resolution,[],[f58641,f317])).
% 27.86/3.96  fof(f317,plain,(
% 27.86/3.96    k1_xboole_0 != k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) | spl11_31),
% 27.86/3.96    inference(avatar_component_clause,[],[f316])).
% 27.86/3.96  fof(f316,plain,(
% 27.86/3.96    spl11_31 <=> k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).
% 27.86/3.96  fof(f58641,plain,(
% 27.86/3.96    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) | (~spl11_11 | ~spl11_22 | ~spl11_1130)),
% 27.86/3.96    inference(forward_demodulation,[],[f58637,f181])).
% 27.86/3.96  fof(f181,plain,(
% 27.86/3.96    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl11_11),
% 27.86/3.96    inference(avatar_component_clause,[],[f180])).
% 27.86/3.96  fof(f180,plain,(
% 27.86/3.96    spl11_11 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 27.86/3.96  fof(f58637,plain,(
% 27.86/3.96    ( ! [X4] : (k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k3_xboole_0(k1_xboole_0,X4)) ) | (~spl11_22 | ~spl11_1130)),
% 27.86/3.96    inference(resolution,[],[f58560,f247])).
% 27.86/3.96  fof(f247,plain,(
% 27.86/3.96    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | k3_xboole_0(X0,X1) = X2) ) | ~spl11_22),
% 27.86/3.96    inference(avatar_component_clause,[],[f246])).
% 27.86/3.96  fof(f246,plain,(
% 27.86/3.96    spl11_22 <=> ! [X1,X0,X2] : (k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2))),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 27.86/3.96  fof(f58560,plain,(
% 27.86/3.96    ( ! [X0] : (sP1(k1_xboole_0,X0,k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))))) ) | ~spl11_1130),
% 27.86/3.96    inference(avatar_component_clause,[],[f58559])).
% 27.86/3.96  fof(f58559,plain,(
% 27.86/3.96    spl11_1130 <=> ! [X0] : sP1(k1_xboole_0,X0,k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_1130])])).
% 27.86/3.96  fof(f58561,plain,(
% 27.86/3.96    spl11_1130 | ~spl11_17 | ~spl11_23 | ~spl11_145 | ~spl11_254),
% 27.86/3.96    inference(avatar_split_clause,[],[f5251,f5237,f3109,f250,f219,f58559])).
% 27.86/3.96  fof(f219,plain,(
% 27.86/3.96    spl11_17 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 27.86/3.96  fof(f250,plain,(
% 27.86/3.96    spl11_23 <=> ! [X1,X0] : ~sP0(X0,X1,k1_xboole_0)),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).
% 27.86/3.96  fof(f3109,plain,(
% 27.86/3.96    spl11_145 <=> ! [X1,X3,X0,X2] : (sP0(X0,sK9(X1,X0,X2),X1) | sP1(X1,X0,X2) | r2_hidden(sK9(X1,X0,X2),X3) | ~r1_tarski(X2,X3))),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_145])])).
% 27.86/3.96  fof(f5237,plain,(
% 27.86/3.96    spl11_254 <=> r1_tarski(k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k1_xboole_0)),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_254])])).
% 27.86/3.96  fof(f5251,plain,(
% 27.86/3.96    ( ! [X0] : (sP1(k1_xboole_0,X0,k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))))) ) | (~spl11_17 | ~spl11_23 | ~spl11_145 | ~spl11_254)),
% 27.86/3.96    inference(unit_resulting_resolution,[],[f220,f251,f5238,f3110])).
% 27.86/3.96  fof(f3110,plain,(
% 27.86/3.96    ( ! [X2,X0,X3,X1] : (sP0(X0,sK9(X1,X0,X2),X1) | r2_hidden(sK9(X1,X0,X2),X3) | sP1(X1,X0,X2) | ~r1_tarski(X2,X3)) ) | ~spl11_145),
% 27.86/3.96    inference(avatar_component_clause,[],[f3109])).
% 27.86/3.96  fof(f5238,plain,(
% 27.86/3.96    r1_tarski(k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k1_xboole_0) | ~spl11_254),
% 27.86/3.96    inference(avatar_component_clause,[],[f5237])).
% 27.86/3.96  fof(f251,plain,(
% 27.86/3.96    ( ! [X0,X1] : (~sP0(X0,X1,k1_xboole_0)) ) | ~spl11_23),
% 27.86/3.96    inference(avatar_component_clause,[],[f250])).
% 27.86/3.96  fof(f220,plain,(
% 27.86/3.96    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl11_17),
% 27.86/3.96    inference(avatar_component_clause,[],[f219])).
% 27.86/3.96  fof(f5239,plain,(
% 27.86/3.96    spl11_254 | ~spl11_8 | ~spl11_88 | ~spl11_103),
% 27.86/3.96    inference(avatar_split_clause,[],[f2677,f2458,f1515,f162,f5237])).
% 27.86/3.96  fof(f162,plain,(
% 27.86/3.96    spl11_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 27.86/3.96  fof(f1515,plain,(
% 27.86/3.96    spl11_88 <=> r1_tarski(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).
% 27.86/3.96  fof(f2458,plain,(
% 27.86/3.96    spl11_103 <=> ! [X1,X0] : (~r1_tarski(X1,X0) | r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0))),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).
% 27.86/3.96  fof(f2677,plain,(
% 27.86/3.96    r1_tarski(k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k1_xboole_0) | (~spl11_8 | ~spl11_88 | ~spl11_103)),
% 27.86/3.96    inference(forward_demodulation,[],[f2672,f163])).
% 27.86/3.96  fof(f163,plain,(
% 27.86/3.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl11_8),
% 27.86/3.96    inference(avatar_component_clause,[],[f162])).
% 27.86/3.96  fof(f2672,plain,(
% 27.86/3.96    r1_tarski(k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)),k1_xboole_0) | (~spl11_88 | ~spl11_103)),
% 27.86/3.96    inference(unit_resulting_resolution,[],[f1516,f2459])).
% 27.86/3.96  fof(f2459,plain,(
% 27.86/3.96    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0) | ~r1_tarski(X1,X0)) ) | ~spl11_103),
% 27.86/3.96    inference(avatar_component_clause,[],[f2458])).
% 27.86/3.96  fof(f1516,plain,(
% 27.86/3.96    r1_tarski(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6) | ~spl11_88),
% 27.86/3.96    inference(avatar_component_clause,[],[f1515])).
% 27.86/3.96  fof(f3111,plain,(
% 27.86/3.96    spl11_145 | ~spl11_20 | ~spl11_79),
% 27.86/3.96    inference(avatar_split_clause,[],[f1216,f1156,f238,f3109])).
% 27.86/3.96  fof(f238,plain,(
% 27.86/3.96    spl11_20 <=> ! [X1,X3,X0] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1))),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 27.86/3.96  fof(f1156,plain,(
% 27.86/3.96    spl11_79 <=> ! [X1,X0,X2] : (sP1(X0,X1,X2) | sP0(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2))),
% 27.86/3.96    introduced(avatar_definition,[new_symbols(naming,[spl11_79])])).
% 27.86/3.96  fof(f1216,plain,(
% 27.86/3.96    ( ! [X2,X0,X3,X1] : (sP0(X0,sK9(X1,X0,X2),X1) | sP1(X1,X0,X2) | r2_hidden(sK9(X1,X0,X2),X3) | ~r1_tarski(X2,X3)) ) | (~spl11_20 | ~spl11_79)),
% 27.86/3.96    inference(resolution,[],[f1157,f239])).
% 27.86/3.96  fof(f239,plain,(
% 27.86/3.96    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) ) | ~spl11_20),
% 27.86/3.96    inference(avatar_component_clause,[],[f238])).
% 27.86/3.97  fof(f1157,plain,(
% 27.86/3.97    ( ! [X2,X0,X1] : (sP0(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2) | sP1(X0,X1,X2)) ) | ~spl11_79),
% 27.86/3.97    inference(avatar_component_clause,[],[f1156])).
% 27.86/3.97  fof(f2460,plain,(
% 27.86/3.97    spl11_103 | ~spl11_56 | ~spl11_82),
% 27.86/3.97    inference(avatar_split_clause,[],[f1331,f1279,f575,f2458])).
% 27.86/3.97  fof(f575,plain,(
% 27.86/3.97    spl11_56 <=> ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0),
% 27.86/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).
% 27.86/3.97  fof(f1279,plain,(
% 27.86/3.97    spl11_82 <=> ! [X1,X0,X2] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | ~r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))),
% 27.86/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).
% 27.86/3.97  fof(f1331,plain,(
% 27.86/3.97    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0)) ) | (~spl11_56 | ~spl11_82)),
% 27.86/3.97    inference(superposition,[],[f1280,f576])).
% 27.86/3.97  fof(f576,plain,(
% 27.86/3.97    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) ) | ~spl11_56),
% 27.86/3.97    inference(avatar_component_clause,[],[f575])).
% 27.86/3.97  fof(f1280,plain,(
% 27.86/3.97    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) ) | ~spl11_82),
% 27.86/3.97    inference(avatar_component_clause,[],[f1279])).
% 27.86/3.97  fof(f2226,plain,(
% 27.86/3.97    ~spl11_5 | ~spl11_43 | ~spl11_60 | ~spl11_61 | ~spl11_63 | ~spl11_95),
% 27.86/3.97    inference(avatar_contradiction_clause,[],[f2225])).
% 27.86/3.97  fof(f2225,plain,(
% 27.86/3.97    $false | (~spl11_5 | ~spl11_43 | ~spl11_60 | ~spl11_61 | ~spl11_63 | ~spl11_95)),
% 27.86/3.97    inference(subsumption_resolution,[],[f2214,f881])).
% 27.86/3.97  fof(f881,plain,(
% 27.86/3.97    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) ) | (~spl11_5 | ~spl11_60 | ~spl11_63)),
% 27.86/3.97    inference(unit_resulting_resolution,[],[f150,f667,f797])).
% 27.86/3.97  fof(f797,plain,(
% 27.86/3.97    ( ! [X2,X0,X5,X3,X1] : (~sP4(X0,X1,X2,X3) | ~sP3(X5,X2,X1,X0) | r2_hidden(X5,X3)) ) | ~spl11_63),
% 27.86/3.97    inference(avatar_component_clause,[],[f796])).
% 27.86/3.97  fof(f796,plain,(
% 27.86/3.97    spl11_63 <=> ! [X1,X3,X5,X0,X2] : (r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0) | ~sP4(X0,X1,X2,X3))),
% 27.86/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).
% 27.86/3.97  fof(f667,plain,(
% 27.86/3.97    ( ! [X2,X0,X1] : (sP4(X0,X1,X2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) ) | ~spl11_60),
% 27.86/3.97    inference(avatar_component_clause,[],[f666])).
% 27.86/3.97  fof(f666,plain,(
% 27.86/3.97    spl11_60 <=> ! [X1,X0,X2] : sP4(X0,X1,X2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))),
% 27.86/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).
% 27.86/3.97  fof(f150,plain,(
% 27.86/3.97    ( ! [X2,X3,X1] : (sP3(X3,X1,X2,X3)) ) | ~spl11_5),
% 27.86/3.97    inference(avatar_component_clause,[],[f149])).
% 27.86/3.97  fof(f149,plain,(
% 27.86/3.97    spl11_5 <=> ! [X1,X3,X2] : sP3(X3,X1,X2,X3)),
% 27.86/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 27.86/3.97  fof(f2214,plain,(
% 27.86/3.97    ~r2_hidden(sK5,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) | (~spl11_43 | ~spl11_61 | ~spl11_95)),
% 27.86/3.97    inference(unit_resulting_resolution,[],[f1908,f671,f413])).
% 27.86/3.97  fof(f413,plain,(
% 27.86/3.97    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) ) | ~spl11_43),
% 27.86/3.97    inference(avatar_component_clause,[],[f412])).
% 27.86/3.97  fof(f412,plain,(
% 27.86/3.97    spl11_43 <=> ! [X1,X0,X2] : (sP2(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2))),
% 27.86/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).
% 27.86/3.97  fof(f671,plain,(
% 27.86/3.97    ( ! [X0] : (~r2_hidden(sK5,k3_xboole_0(sK6,X0))) ) | ~spl11_61),
% 27.86/3.97    inference(avatar_component_clause,[],[f670])).
% 27.86/3.97  fof(f670,plain,(
% 27.86/3.97    spl11_61 <=> ! [X0] : ~r2_hidden(sK5,k3_xboole_0(sK6,X0))),
% 27.86/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).
% 27.86/3.97  fof(f1908,plain,(
% 27.86/3.97    ( ! [X0] : (~sP2(k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ) | ~spl11_95),
% 27.86/3.97    inference(avatar_component_clause,[],[f1907])).
% 27.86/3.97  fof(f1907,plain,(
% 27.86/3.97    spl11_95 <=> ! [X0] : ~sP2(k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))),
% 27.86/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_95])])).
% 28.64/3.97  fof(f1909,plain,(
% 28.64/3.97    spl11_95 | ~spl11_17 | ~spl11_26 | ~spl11_31),
% 28.64/3.97    inference(avatar_split_clause,[],[f1795,f316,f262,f219,f1907])).
% 28.64/3.97  fof(f262,plain,(
% 28.64/3.97    spl11_26 <=> ! [X1,X0,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1))),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).
% 28.64/3.97  fof(f1795,plain,(
% 28.64/3.97    ( ! [X0] : (~sP2(k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ) | (~spl11_17 | ~spl11_26 | ~spl11_31)),
% 28.64/3.97    inference(subsumption_resolution,[],[f1793,f220])).
% 28.64/3.97  fof(f1793,plain,(
% 28.64/3.97    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP2(k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ) | (~spl11_26 | ~spl11_31)),
% 28.64/3.97    inference(superposition,[],[f263,f361])).
% 28.64/3.97  fof(f361,plain,(
% 28.64/3.97    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) | ~spl11_31),
% 28.64/3.97    inference(avatar_component_clause,[],[f316])).
% 28.64/3.97  fof(f263,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) ) | ~spl11_26),
% 28.64/3.97    inference(avatar_component_clause,[],[f262])).
% 28.64/3.97  fof(f1517,plain,(
% 28.64/3.97    spl11_88 | ~spl11_30 | ~spl11_65),
% 28.64/3.97    inference(avatar_split_clause,[],[f1415,f824,f311,f1515])).
% 28.64/3.97  fof(f311,plain,(
% 28.64/3.97    spl11_30 <=> r2_hidden(sK5,sK6)),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).
% 28.64/3.97  fof(f824,plain,(
% 28.64/3.97    spl11_65 <=> ! [X1,X0] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1))),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).
% 28.64/3.97  fof(f1415,plain,(
% 28.64/3.97    r1_tarski(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6) | (~spl11_30 | ~spl11_65)),
% 28.64/3.97    inference(unit_resulting_resolution,[],[f320,f825])).
% 28.64/3.97  fof(f825,plain,(
% 28.64/3.97    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl11_65),
% 28.64/3.97    inference(avatar_component_clause,[],[f824])).
% 28.64/3.97  fof(f320,plain,(
% 28.64/3.97    r2_hidden(sK5,sK6) | ~spl11_30),
% 28.64/3.97    inference(avatar_component_clause,[],[f311])).
% 28.64/3.97  fof(f1281,plain,(
% 28.64/3.97    spl11_82),
% 28.64/3.97    inference(avatar_split_clause,[],[f124,f1279])).
% 28.64/3.97  fof(f124,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | ~r1_tarski(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) )),
% 28.64/3.97    inference(definition_unfolding,[],[f84,f75,f117])).
% 28.64/3.97  fof(f117,plain,(
% 28.64/3.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 28.64/3.97    inference(definition_unfolding,[],[f73,f116])).
% 28.64/3.97  fof(f116,plain,(
% 28.64/3.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 28.64/3.97    inference(definition_unfolding,[],[f74,f115])).
% 28.64/3.97  fof(f115,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 28.64/3.97    inference(definition_unfolding,[],[f83,f114])).
% 28.64/3.97  fof(f114,plain,(
% 28.64/3.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 28.64/3.97    inference(definition_unfolding,[],[f100,f113])).
% 28.64/3.97  fof(f113,plain,(
% 28.64/3.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 28.64/3.97    inference(definition_unfolding,[],[f111,f112])).
% 28.64/3.97  fof(f112,plain,(
% 28.64/3.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f17])).
% 28.64/3.97  fof(f17,axiom,(
% 28.64/3.97    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 28.64/3.97  fof(f111,plain,(
% 28.64/3.97    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f16])).
% 28.64/3.97  fof(f16,axiom,(
% 28.64/3.97    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 28.64/3.97  fof(f100,plain,(
% 28.64/3.97    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f15])).
% 28.64/3.97  fof(f15,axiom,(
% 28.64/3.97    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 28.64/3.97  fof(f83,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f14])).
% 28.64/3.97  fof(f14,axiom,(
% 28.64/3.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 28.64/3.97  fof(f74,plain,(
% 28.64/3.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f13])).
% 28.64/3.97  fof(f13,axiom,(
% 28.64/3.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 28.64/3.97  fof(f73,plain,(
% 28.64/3.97    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f19])).
% 28.64/3.97  fof(f19,axiom,(
% 28.64/3.97    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 28.64/3.97  fof(f75,plain,(
% 28.64/3.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 28.64/3.97    inference(cnf_transformation,[],[f6])).
% 28.64/3.97  fof(f6,axiom,(
% 28.64/3.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 28.64/3.97  fof(f84,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 28.64/3.97    inference(cnf_transformation,[],[f26])).
% 28.64/3.97  fof(f26,plain,(
% 28.64/3.97    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 28.64/3.97    inference(ennf_transformation,[],[f9])).
% 28.64/3.97  fof(f9,axiom,(
% 28.64/3.97    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 28.64/3.97  fof(f1158,plain,(
% 28.64/3.97    spl11_79),
% 28.64/3.97    inference(avatar_split_clause,[],[f87,f1156])).
% 28.64/3.97  fof(f87,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | sP0(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f50])).
% 28.64/3.97  fof(f50,plain,(
% 28.64/3.97    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP0(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 28.64/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).
% 28.64/3.97  fof(f49,plain,(
% 28.64/3.97    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP0(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 28.64/3.97    introduced(choice_axiom,[])).
% 28.64/3.97  fof(f48,plain,(
% 28.64/3.97    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 28.64/3.97    inference(rectify,[],[f47])).
% 28.64/3.97  fof(f47,plain,(
% 28.64/3.97    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 28.64/3.97    inference(nnf_transformation,[],[f30])).
% 28.64/3.97  fof(f30,plain,(
% 28.64/3.97    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 28.64/3.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 28.64/3.97  fof(f826,plain,(
% 28.64/3.97    spl11_65),
% 28.64/3.97    inference(avatar_split_clause,[],[f122,f824])).
% 28.64/3.97  fof(f122,plain,(
% 28.64/3.97    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 28.64/3.97    inference(definition_unfolding,[],[f82,f118])).
% 28.64/3.97  fof(f118,plain,(
% 28.64/3.97    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 28.64/3.97    inference(definition_unfolding,[],[f71,f116])).
% 28.64/3.97  fof(f71,plain,(
% 28.64/3.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f12])).
% 28.64/3.97  fof(f12,axiom,(
% 28.64/3.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 28.64/3.97  fof(f82,plain,(
% 28.64/3.97    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f46])).
% 28.64/3.97  fof(f46,plain,(
% 28.64/3.97    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 28.64/3.97    inference(nnf_transformation,[],[f18])).
% 28.64/3.97  fof(f18,axiom,(
% 28.64/3.97    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 28.64/3.97  fof(f798,plain,(
% 28.64/3.97    spl11_63),
% 28.64/3.97    inference(avatar_split_clause,[],[f102,f796])).
% 28.64/3.97  fof(f102,plain,(
% 28.64/3.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0) | ~sP4(X0,X1,X2,X3)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f61])).
% 28.64/3.97  fof(f61,plain,(
% 28.64/3.97    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ((~sP3(sK10(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK10(X0,X1,X2,X3),X3)) & (sP3(sK10(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK10(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 28.64/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f59,f60])).
% 28.64/3.97  fof(f60,plain,(
% 28.64/3.97    ! [X3,X2,X1,X0] : (? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP3(sK10(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK10(X0,X1,X2,X3),X3)) & (sP3(sK10(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK10(X0,X1,X2,X3),X3))))),
% 28.64/3.97    introduced(choice_axiom,[])).
% 28.64/3.97  fof(f59,plain,(
% 28.64/3.97    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 28.64/3.97    inference(rectify,[],[f58])).
% 28.64/3.97  fof(f58,plain,(
% 28.64/3.97    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP3(X4,X2,X1,X0)) & (sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP4(X0,X1,X2,X3)))),
% 28.64/3.97    inference(nnf_transformation,[],[f35])).
% 28.64/3.97  fof(f35,plain,(
% 28.64/3.97    ! [X0,X1,X2,X3] : (sP4(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP3(X4,X2,X1,X0)))),
% 28.64/3.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 28.64/3.97  fof(f672,plain,(
% 28.64/3.97    spl11_61 | ~spl11_13 | ~spl11_38 | ~spl11_52),
% 28.64/3.97    inference(avatar_split_clause,[],[f593,f529,f364,f193,f670])).
% 28.64/3.97  fof(f193,plain,(
% 28.64/3.97    spl11_13 <=> ! [X1,X2] : sP1(X1,X2,k3_xboole_0(X2,X1))),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 28.64/3.97  fof(f364,plain,(
% 28.64/3.97    spl11_38 <=> ! [X0] : ~sP0(sK6,sK5,X0)),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).
% 28.64/3.97  fof(f529,plain,(
% 28.64/3.97    spl11_52 <=> ! [X1,X0,X2,X4] : (sP0(X1,X4,X0) | ~r2_hidden(X4,X2) | ~sP1(X0,X1,X2))),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).
% 28.64/3.97  fof(f593,plain,(
% 28.64/3.97    ( ! [X0] : (~r2_hidden(sK5,k3_xboole_0(sK6,X0))) ) | (~spl11_13 | ~spl11_38 | ~spl11_52)),
% 28.64/3.97    inference(unit_resulting_resolution,[],[f365,f194,f530])).
% 28.64/3.97  fof(f530,plain,(
% 28.64/3.97    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) ) | ~spl11_52),
% 28.64/3.97    inference(avatar_component_clause,[],[f529])).
% 28.64/3.97  fof(f194,plain,(
% 28.64/3.97    ( ! [X2,X1] : (sP1(X1,X2,k3_xboole_0(X2,X1))) ) | ~spl11_13),
% 28.64/3.97    inference(avatar_component_clause,[],[f193])).
% 28.64/3.97  fof(f365,plain,(
% 28.64/3.97    ( ! [X0] : (~sP0(sK6,sK5,X0)) ) | ~spl11_38),
% 28.64/3.97    inference(avatar_component_clause,[],[f364])).
% 28.64/3.97  fof(f668,plain,(
% 28.64/3.97    spl11_60),
% 28.64/3.97    inference(avatar_split_clause,[],[f131,f666])).
% 28.64/3.97  fof(f131,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (sP4(X0,X1,X2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 28.64/3.97    inference(equality_resolution,[],[f126])).
% 28.64/3.97  fof(f126,plain,(
% 28.64/3.97    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 28.64/3.97    inference(definition_unfolding,[],[f109,f115])).
% 28.64/3.97  fof(f109,plain,(
% 28.64/3.97    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 28.64/3.97    inference(cnf_transformation,[],[f65])).
% 28.64/3.97  fof(f65,plain,(
% 28.64/3.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) & (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 28.64/3.97    inference(nnf_transformation,[],[f36])).
% 28.64/3.97  fof(f36,plain,(
% 28.64/3.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP4(X0,X1,X2,X3))),
% 28.64/3.97    inference(definition_folding,[],[f28,f35,f34])).
% 28.64/3.97  fof(f34,plain,(
% 28.64/3.97    ! [X4,X2,X1,X0] : (sP3(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 28.64/3.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 28.64/3.97  fof(f28,plain,(
% 28.64/3.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 28.64/3.97    inference(ennf_transformation,[],[f11])).
% 28.64/3.97  fof(f11,axiom,(
% 28.64/3.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 28.64/3.97  fof(f577,plain,(
% 28.64/3.97    spl11_56),
% 28.64/3.97    inference(avatar_split_clause,[],[f121,f575])).
% 28.64/3.97  fof(f121,plain,(
% 28.64/3.97    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 28.64/3.97    inference(definition_unfolding,[],[f70,f117])).
% 28.64/3.97  fof(f70,plain,(
% 28.64/3.97    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 28.64/3.97    inference(cnf_transformation,[],[f7])).
% 28.64/3.97  fof(f7,axiom,(
% 28.64/3.97    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 28.64/3.97  fof(f531,plain,(
% 28.64/3.97    spl11_52),
% 28.64/3.97    inference(avatar_split_clause,[],[f85,f529])).
% 28.64/3.97  fof(f85,plain,(
% 28.64/3.97    ( ! [X4,X2,X0,X1] : (sP0(X1,X4,X0) | ~r2_hidden(X4,X2) | ~sP1(X0,X1,X2)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f50])).
% 28.64/3.97  fof(f414,plain,(
% 28.64/3.97    spl11_43),
% 28.64/3.97    inference(avatar_split_clause,[],[f96,f412])).
% 28.64/3.97  fof(f96,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f56])).
% 28.64/3.97  fof(f56,plain,(
% 28.64/3.97    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP2(X0,X1,X2)))),
% 28.64/3.97    inference(rectify,[],[f55])).
% 28.64/3.97  fof(f55,plain,(
% 28.64/3.97    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP2(X2,X0,X1)))),
% 28.64/3.97    inference(nnf_transformation,[],[f32])).
% 28.64/3.97  fof(f32,plain,(
% 28.64/3.97    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 28.64/3.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 28.64/3.97  fof(f366,plain,(
% 28.64/3.97    spl11_38 | ~spl11_10 | spl11_30),
% 28.64/3.97    inference(avatar_split_clause,[],[f359,f311,f170,f364])).
% 28.64/3.97  fof(f170,plain,(
% 28.64/3.97    spl11_10 <=> ! [X1,X0,X2] : (r2_hidden(X1,X0) | ~sP0(X0,X1,X2))),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 28.64/3.97  fof(f359,plain,(
% 28.64/3.97    ( ! [X0] : (~sP0(sK6,sK5,X0)) ) | (~spl11_10 | spl11_30)),
% 28.64/3.97    inference(unit_resulting_resolution,[],[f312,f171])).
% 28.64/3.97  fof(f171,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X0)) ) | ~spl11_10),
% 28.64/3.97    inference(avatar_component_clause,[],[f170])).
% 28.64/3.97  fof(f312,plain,(
% 28.64/3.97    ~r2_hidden(sK5,sK6) | spl11_30),
% 28.64/3.97    inference(avatar_component_clause,[],[f311])).
% 28.64/3.97  fof(f362,plain,(
% 28.64/3.97    spl11_31 | ~spl11_8 | ~spl11_29),
% 28.64/3.97    inference(avatar_split_clause,[],[f354,f308,f162,f316])).
% 28.64/3.97  fof(f308,plain,(
% 28.64/3.97    spl11_29 <=> k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).
% 28.64/3.97  fof(f354,plain,(
% 28.64/3.97    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) | (~spl11_8 | ~spl11_29)),
% 28.64/3.97    inference(forward_demodulation,[],[f319,f163])).
% 28.64/3.97  fof(f319,plain,(
% 28.64/3.97    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)) | ~spl11_29),
% 28.64/3.97    inference(avatar_component_clause,[],[f308])).
% 28.64/3.97  fof(f321,plain,(
% 28.64/3.97    spl11_29 | spl11_30),
% 28.64/3.97    inference(avatar_split_clause,[],[f120,f311,f308])).
% 28.64/3.97  fof(f120,plain,(
% 28.64/3.97    r2_hidden(sK5,sK6) | k1_xboole_0 = k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))),
% 28.64/3.97    inference(definition_unfolding,[],[f66,f75,f118])).
% 28.64/3.97  fof(f66,plain,(
% 28.64/3.97    r2_hidden(sK5,sK6) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6)),
% 28.64/3.97    inference(cnf_transformation,[],[f39])).
% 28.64/3.97  fof(f39,plain,(
% 28.64/3.97    (~r2_hidden(sK5,sK6) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6)) & (r2_hidden(sK5,sK6) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6))),
% 28.64/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f37,f38])).
% 28.64/3.97  fof(f38,plain,(
% 28.64/3.97    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK5,sK6) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6)) & (r2_hidden(sK5,sK6) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6)))),
% 28.64/3.97    introduced(choice_axiom,[])).
% 28.64/3.97  fof(f37,plain,(
% 28.64/3.97    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 28.64/3.97    inference(nnf_transformation,[],[f23])).
% 28.64/3.97  fof(f23,plain,(
% 28.64/3.97    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 28.64/3.97    inference(ennf_transformation,[],[f21])).
% 28.64/3.97  fof(f21,negated_conjecture,(
% 28.64/3.97    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 28.64/3.97    inference(negated_conjecture,[],[f20])).
% 28.64/3.97  fof(f20,conjecture,(
% 28.64/3.97    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 28.64/3.97  fof(f318,plain,(
% 28.64/3.97    ~spl11_31 | ~spl11_8 | spl11_29),
% 28.64/3.97    inference(avatar_split_clause,[],[f314,f308,f162,f316])).
% 28.64/3.97  fof(f314,plain,(
% 28.64/3.97    k1_xboole_0 != k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK6,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) | (~spl11_8 | spl11_29)),
% 28.64/3.97    inference(forward_demodulation,[],[f309,f163])).
% 28.64/3.97  fof(f309,plain,(
% 28.64/3.97    k1_xboole_0 != k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)) | spl11_29),
% 28.64/3.97    inference(avatar_component_clause,[],[f308])).
% 28.64/3.97  fof(f313,plain,(
% 28.64/3.97    ~spl11_29 | ~spl11_30),
% 28.64/3.97    inference(avatar_split_clause,[],[f119,f311,f308])).
% 28.64/3.97  fof(f119,plain,(
% 28.64/3.97    ~r2_hidden(sK5,sK6) | k1_xboole_0 != k5_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))),
% 28.64/3.97    inference(definition_unfolding,[],[f67,f75,f118])).
% 28.64/3.97  fof(f67,plain,(
% 28.64/3.97    ~r2_hidden(sK5,sK6) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6)),
% 28.64/3.97    inference(cnf_transformation,[],[f39])).
% 28.64/3.97  fof(f264,plain,(
% 28.64/3.97    spl11_26),
% 28.64/3.97    inference(avatar_split_clause,[],[f99,f262])).
% 28.64/3.97  fof(f99,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f57])).
% 28.64/3.97  fof(f57,plain,(
% 28.64/3.97    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 28.64/3.97    inference(nnf_transformation,[],[f33])).
% 28.64/3.97  fof(f33,plain,(
% 28.64/3.97    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP2(X2,X0,X1))),
% 28.64/3.97    inference(definition_folding,[],[f27,f32])).
% 28.64/3.97  fof(f27,plain,(
% 28.64/3.97    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 28.64/3.97    inference(ennf_transformation,[],[f4])).
% 28.64/3.97  fof(f4,axiom,(
% 28.64/3.97    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 28.64/3.97  fof(f252,plain,(
% 28.64/3.97    spl11_23 | ~spl11_9 | ~spl11_17),
% 28.64/3.97    inference(avatar_split_clause,[],[f224,f219,f166,f250])).
% 28.64/3.97  fof(f166,plain,(
% 28.64/3.97    spl11_9 <=> ! [X1,X0,X2] : (r2_hidden(X1,X2) | ~sP0(X0,X1,X2))),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 28.64/3.97  fof(f224,plain,(
% 28.64/3.97    ( ! [X0,X1] : (~sP0(X0,X1,k1_xboole_0)) ) | (~spl11_9 | ~spl11_17)),
% 28.64/3.97    inference(unit_resulting_resolution,[],[f220,f167])).
% 28.64/3.97  fof(f167,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) ) | ~spl11_9),
% 28.64/3.97    inference(avatar_component_clause,[],[f166])).
% 28.64/3.97  fof(f248,plain,(
% 28.64/3.97    spl11_22),
% 28.64/3.97    inference(avatar_split_clause,[],[f93,f246])).
% 28.64/3.97  fof(f93,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f54])).
% 28.64/3.97  fof(f54,plain,(
% 28.64/3.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 28.64/3.97    inference(nnf_transformation,[],[f31])).
% 28.64/3.97  fof(f31,plain,(
% 28.64/3.97    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 28.64/3.97    inference(definition_folding,[],[f3,f30,f29])).
% 28.64/3.97  fof(f29,plain,(
% 28.64/3.97    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 28.64/3.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 28.64/3.97  fof(f3,axiom,(
% 28.64/3.97    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 28.64/3.97  fof(f240,plain,(
% 28.64/3.97    spl11_20),
% 28.64/3.97    inference(avatar_split_clause,[],[f78,f238])).
% 28.64/3.97  fof(f78,plain,(
% 28.64/3.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f45])).
% 28.64/3.97  fof(f45,plain,(
% 28.64/3.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 28.64/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f43,f44])).
% 28.64/3.97  fof(f44,plain,(
% 28.64/3.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 28.64/3.97    introduced(choice_axiom,[])).
% 28.64/3.97  fof(f43,plain,(
% 28.64/3.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 28.64/3.97    inference(rectify,[],[f42])).
% 28.64/3.97  fof(f42,plain,(
% 28.64/3.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 28.64/3.97    inference(nnf_transformation,[],[f25])).
% 28.64/3.97  fof(f25,plain,(
% 28.64/3.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 28.64/3.97    inference(ennf_transformation,[],[f2])).
% 28.64/3.97  fof(f2,axiom,(
% 28.64/3.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 28.64/3.97  fof(f221,plain,(
% 28.64/3.97    spl11_17 | ~spl11_1 | ~spl11_2 | ~spl11_14),
% 28.64/3.97    inference(avatar_split_clause,[],[f217,f197,f137,f133,f219])).
% 28.64/3.97  fof(f133,plain,(
% 28.64/3.97    spl11_1 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 28.64/3.97  fof(f137,plain,(
% 28.64/3.97    spl11_2 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 28.64/3.97  fof(f197,plain,(
% 28.64/3.97    spl11_14 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 28.64/3.97  fof(f217,plain,(
% 28.64/3.97    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl11_1 | ~spl11_2 | ~spl11_14)),
% 28.64/3.97    inference(forward_demodulation,[],[f212,f138])).
% 28.64/3.97  fof(f138,plain,(
% 28.64/3.97    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl11_2),
% 28.64/3.97    inference(avatar_component_clause,[],[f137])).
% 28.64/3.97  fof(f212,plain,(
% 28.64/3.97    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) ) | (~spl11_1 | ~spl11_14)),
% 28.64/3.97    inference(unit_resulting_resolution,[],[f134,f198])).
% 28.64/3.97  fof(f198,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl11_14),
% 28.64/3.97    inference(avatar_component_clause,[],[f197])).
% 28.64/3.97  fof(f134,plain,(
% 28.64/3.97    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl11_1),
% 28.64/3.97    inference(avatar_component_clause,[],[f133])).
% 28.64/3.97  fof(f199,plain,(
% 28.64/3.97    spl11_14),
% 28.64/3.97    inference(avatar_split_clause,[],[f77,f197])).
% 28.64/3.97  fof(f77,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 28.64/3.97    inference(cnf_transformation,[],[f41])).
% 28.64/3.97  fof(f41,plain,(
% 28.64/3.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 28.64/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f40])).
% 28.64/3.97  fof(f40,plain,(
% 28.64/3.97    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)))),
% 28.64/3.97    introduced(choice_axiom,[])).
% 28.64/3.97  fof(f24,plain,(
% 28.64/3.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 28.64/3.97    inference(ennf_transformation,[],[f22])).
% 28.64/3.97  fof(f22,plain,(
% 28.64/3.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 28.64/3.97    inference(rectify,[],[f5])).
% 28.64/3.97  fof(f5,axiom,(
% 28.64/3.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 28.64/3.97  fof(f195,plain,(
% 28.64/3.97    spl11_13 | ~spl11_6 | ~spl11_8),
% 28.64/3.97    inference(avatar_split_clause,[],[f176,f162,f153,f193])).
% 28.64/3.97  fof(f153,plain,(
% 28.64/3.97    spl11_6 <=> ! [X1,X0] : sP1(X0,X1,k3_xboole_0(X0,X1))),
% 28.64/3.97    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 28.64/3.97  fof(f176,plain,(
% 28.64/3.97    ( ! [X2,X1] : (sP1(X1,X2,k3_xboole_0(X2,X1))) ) | (~spl11_6 | ~spl11_8)),
% 28.64/3.97    inference(superposition,[],[f154,f163])).
% 28.64/3.97  fof(f154,plain,(
% 28.64/3.97    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X0,X1))) ) | ~spl11_6),
% 28.64/3.97    inference(avatar_component_clause,[],[f153])).
% 28.64/3.97  fof(f182,plain,(
% 28.64/3.97    spl11_11 | ~spl11_2 | ~spl11_8),
% 28.64/3.97    inference(avatar_split_clause,[],[f173,f162,f137,f180])).
% 28.64/3.97  fof(f173,plain,(
% 28.64/3.97    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl11_2 | ~spl11_8)),
% 28.64/3.97    inference(superposition,[],[f163,f138])).
% 28.64/3.97  fof(f172,plain,(
% 28.64/3.97    spl11_10),
% 28.64/3.97    inference(avatar_split_clause,[],[f90,f170])).
% 28.64/3.97  fof(f90,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (r2_hidden(X1,X0) | ~sP0(X0,X1,X2)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f53])).
% 28.64/3.97  fof(f53,plain,(
% 28.64/3.97    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 28.64/3.97    inference(rectify,[],[f52])).
% 28.64/3.97  fof(f52,plain,(
% 28.64/3.97    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 28.64/3.97    inference(flattening,[],[f51])).
% 28.64/3.97  fof(f51,plain,(
% 28.64/3.97    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 28.64/3.97    inference(nnf_transformation,[],[f29])).
% 28.64/3.97  fof(f168,plain,(
% 28.64/3.97    spl11_9),
% 28.64/3.97    inference(avatar_split_clause,[],[f89,f166])).
% 28.64/3.97  fof(f89,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~sP0(X0,X1,X2)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f53])).
% 28.64/3.97  fof(f164,plain,(
% 28.64/3.97    spl11_8),
% 28.64/3.97    inference(avatar_split_clause,[],[f72,f162])).
% 28.64/3.97  fof(f72,plain,(
% 28.64/3.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f1])).
% 28.64/3.97  fof(f1,axiom,(
% 28.64/3.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 28.64/3.97  fof(f155,plain,(
% 28.64/3.97    spl11_6),
% 28.64/3.97    inference(avatar_split_clause,[],[f127,f153])).
% 28.64/3.97  fof(f127,plain,(
% 28.64/3.97    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X0,X1))) )),
% 28.64/3.97    inference(equality_resolution,[],[f92])).
% 28.64/3.97  fof(f92,plain,(
% 28.64/3.97    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 28.64/3.97    inference(cnf_transformation,[],[f54])).
% 28.64/3.97  fof(f151,plain,(
% 28.64/3.97    spl11_5),
% 28.64/3.97    inference(avatar_split_clause,[],[f130,f149])).
% 28.64/3.97  fof(f130,plain,(
% 28.64/3.97    ( ! [X2,X3,X1] : (sP3(X3,X1,X2,X3)) )),
% 28.64/3.97    inference(equality_resolution,[],[f106])).
% 28.64/3.97  fof(f106,plain,(
% 28.64/3.97    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | X0 != X3) )),
% 28.64/3.97    inference(cnf_transformation,[],[f64])).
% 28.64/3.97  fof(f64,plain,(
% 28.64/3.97    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP3(X0,X1,X2,X3)))),
% 28.64/3.97    inference(rectify,[],[f63])).
% 28.64/3.97  fof(f63,plain,(
% 28.64/3.97    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP3(X4,X2,X1,X0)))),
% 28.64/3.97    inference(flattening,[],[f62])).
% 28.64/3.97  fof(f62,plain,(
% 28.64/3.97    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP3(X4,X2,X1,X0)))),
% 28.64/3.97    inference(nnf_transformation,[],[f34])).
% 28.64/3.97  fof(f139,plain,(
% 28.64/3.97    spl11_2),
% 28.64/3.97    inference(avatar_split_clause,[],[f69,f137])).
% 28.64/3.97  fof(f69,plain,(
% 28.64/3.97    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f8])).
% 28.64/3.97  fof(f8,axiom,(
% 28.64/3.97    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 28.64/3.97  fof(f135,plain,(
% 28.64/3.97    spl11_1),
% 28.64/3.97    inference(avatar_split_clause,[],[f68,f133])).
% 28.64/3.97  fof(f68,plain,(
% 28.64/3.97    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 28.64/3.97    inference(cnf_transformation,[],[f10])).
% 28.64/3.97  fof(f10,axiom,(
% 28.64/3.97    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 28.64/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 28.64/3.97  % SZS output end Proof for theBenchmark
% 28.64/3.97  % (11759)------------------------------
% 28.64/3.97  % (11759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.64/3.97  % (11759)Termination reason: Refutation
% 28.64/3.97  
% 28.64/3.97  % (11759)Memory used [KB]: 58847
% 28.64/3.97  % (11759)Time elapsed: 2.513 s
% 28.64/3.97  % (11759)------------------------------
% 28.64/3.97  % (11759)------------------------------
% 28.64/3.98  % (11690)Success in time 3.608 s
%------------------------------------------------------------------------------
