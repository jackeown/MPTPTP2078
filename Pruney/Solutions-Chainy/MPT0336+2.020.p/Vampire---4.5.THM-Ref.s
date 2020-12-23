%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 227 expanded)
%              Number of leaves         :   40 ( 106 expanded)
%              Depth                    :    7
%              Number of atoms          :  370 ( 620 expanded)
%              Number of equality atoms :   59 (  98 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3067,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f76,f84,f88,f92,f112,f116,f120,f124,f132,f136,f146,f165,f202,f313,f383,f417,f453,f648,f766,f1504,f1820,f1935,f3031,f3064])).

fof(f3064,plain,
    ( ~ spl5_5
    | ~ spl5_8
    | ~ spl5_21
    | ~ spl5_45
    | spl5_60
    | spl5_81
    | ~ spl5_97
    | ~ spl5_101
    | ~ spl5_137 ),
    inference(avatar_contradiction_clause,[],[f3063])).

fof(f3063,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_21
    | ~ spl5_45
    | spl5_60
    | spl5_81
    | ~ spl5_97
    | ~ spl5_101
    | ~ spl5_137 ),
    inference(subsumption_resolution,[],[f1950,f3062])).

fof(f3062,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl5_5
    | ~ spl5_8
    | spl5_81
    | ~ spl5_97
    | ~ spl5_137 ),
    inference(forward_demodulation,[],[f3044,f1823])).

fof(f1823,plain,
    ( ! [X2] : k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k2_xboole_0(X2,sK2))
    | ~ spl5_8
    | ~ spl5_97 ),
    inference(superposition,[],[f1819,f87])).

fof(f87,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1819,plain,
    ( ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0)
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f1818])).

fof(f1818,plain,
    ( spl5_97
  <=> ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f3044,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)))
    | ~ spl5_5
    | spl5_81
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f1503,f75,f3030])).

fof(f3030,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,X2)
        | X2 = X3
        | ~ r1_tarski(X2,X3) )
    | ~ spl5_137 ),
    inference(avatar_component_clause,[],[f3029])).

fof(f3029,plain,
    ( spl5_137
  <=> ! [X3,X2] :
        ( X2 = X3
        | ~ r1_tarski(X3,X2)
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f75,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_5
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1503,plain,
    ( sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl5_81 ),
    inference(avatar_component_clause,[],[f1501])).

fof(f1501,plain,
    ( spl5_81
  <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f1950,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl5_21
    | ~ spl5_45
    | spl5_60
    | ~ spl5_101 ),
    inference(forward_demodulation,[],[f1944,f948])).

fof(f948,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_21
    | spl5_60 ),
    inference(unit_resulting_resolution,[],[f765,f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f765,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl5_60 ),
    inference(avatar_component_clause,[],[f763])).

fof(f763,plain,
    ( spl5_60
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f1944,plain,
    ( r1_tarski(k4_xboole_0(sK1,k1_tarski(sK3)),k4_xboole_0(sK1,sK0))
    | ~ spl5_45
    | ~ spl5_101 ),
    inference(superposition,[],[f1934,f416])).

fof(f416,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl5_45
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f1934,plain,
    ( ! [X12] : r1_tarski(k4_xboole_0(X12,k1_tarski(sK3)),k4_xboole_0(X12,k3_xboole_0(sK0,sK1)))
    | ~ spl5_101 ),
    inference(avatar_component_clause,[],[f1933])).

fof(f1933,plain,
    ( spl5_101
  <=> ! [X12] : r1_tarski(k4_xboole_0(X12,k1_tarski(sK3)),k4_xboole_0(X12,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f3031,plain,
    ( spl5_137
    | ~ spl5_14
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f388,f381,f114,f3029])).

fof(f114,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f381,plain,
    ( spl5_43
  <=> ! [X3,X2] :
        ( k2_xboole_0(X3,X2) = X3
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f388,plain,
    ( ! [X2,X3] :
        ( X2 = X3
        | ~ r1_tarski(X3,X2)
        | ~ r1_tarski(X2,X3) )
    | ~ spl5_14
    | ~ spl5_43 ),
    inference(superposition,[],[f382,f115])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f114])).

fof(f382,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(X3,X2) = X3
        | ~ r1_tarski(X2,X3) )
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f381])).

fof(f1935,plain,
    ( spl5_101
    | ~ spl5_34
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f460,f451,f310,f1933])).

fof(f310,plain,
    ( spl5_34
  <=> k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f451,plain,
    ( spl5_47
  <=> ! [X9,X11,X10] : r1_tarski(k4_xboole_0(X9,k2_xboole_0(X10,X11)),k4_xboole_0(X9,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f460,plain,
    ( ! [X12] : r1_tarski(k4_xboole_0(X12,k1_tarski(sK3)),k4_xboole_0(X12,k3_xboole_0(sK0,sK1)))
    | ~ spl5_34
    | ~ spl5_47 ),
    inference(superposition,[],[f452,f312])).

fof(f312,plain,
    ( k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f310])).

fof(f452,plain,
    ( ! [X10,X11,X9] : r1_tarski(k4_xboole_0(X9,k2_xboole_0(X10,X11)),k4_xboole_0(X9,X10))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f451])).

fof(f1820,plain,
    ( spl5_97
    | ~ spl5_13
    | ~ spl5_57 ),
    inference(avatar_split_clause,[],[f650,f646,f109,f1818])).

fof(f109,plain,
    ( spl5_13
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f646,plain,
    ( spl5_57
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f650,plain,
    ( ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0)
    | ~ spl5_13
    | ~ spl5_57 ),
    inference(unit_resulting_resolution,[],[f111,f647])).

fof(f647,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f646])).

fof(f111,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1504,plain,
    ( ~ spl5_81
    | ~ spl5_16
    | spl5_22 ),
    inference(avatar_split_clause,[],[f240,f162,f122,f1501])).

fof(f122,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f162,plain,
    ( spl5_22
  <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f240,plain,
    ( sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl5_16
    | spl5_22 ),
    inference(unit_resulting_resolution,[],[f164,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f122])).

fof(f164,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f162])).

fof(f766,plain,
    ( ~ spl5_60
    | ~ spl5_1
    | ~ spl5_13
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f187,f134,f109,f54,f763])).

fof(f54,plain,
    ( spl5_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f134,plain,
    ( spl5_19
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f187,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl5_1
    | ~ spl5_13
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f111,f56,f135])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f134])).

fof(f56,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f648,plain,
    ( spl5_57
    | ~ spl5_15
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f212,f200,f118,f646])).

fof(f118,plain,
    ( spl5_15
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f200,plain,
    ( spl5_24
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f212,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_15
    | ~ spl5_24 ),
    inference(superposition,[],[f201,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f201,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f200])).

fof(f453,plain,
    ( spl5_47
    | ~ spl5_5
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f224,f200,f74,f451])).

fof(f224,plain,
    ( ! [X10,X11,X9] : r1_tarski(k4_xboole_0(X9,k2_xboole_0(X10,X11)),k4_xboole_0(X9,X10))
    | ~ spl5_5
    | ~ spl5_24 ),
    inference(superposition,[],[f75,f201])).

fof(f417,plain,
    ( spl5_45
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f177,f130,f90,f415])).

fof(f90,plain,
    ( spl5_9
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f130,plain,
    ( spl5_18
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f177,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(superposition,[],[f131,f91])).

fof(f91,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f131,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f130])).

fof(f383,plain,
    ( spl5_43
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f151,f114,f86,f381])).

fof(f151,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(X3,X2) = X3
        | ~ r1_tarski(X2,X3) )
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(superposition,[],[f115,f87])).

fof(f313,plain,
    ( spl5_34
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f149,f114,f69,f310])).

fof(f69,plain,
    ( spl5_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f149,plain,
    ( k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f71,f115])).

fof(f71,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f202,plain,(
    spl5_24 ),
    inference(avatar_split_clause,[],[f51,f200])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f165,plain,
    ( ~ spl5_22
    | spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f93,f82,f64,f162])).

fof(f64,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f82,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f93,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl5_3
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f66,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f66,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f146,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f49,f144])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f136,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f43,f134])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f132,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f40,f130])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f124,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f47,f122])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f120,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f46,f118])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f116,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f44,f114])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f112,plain,
    ( spl5_13
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f94,f82,f59,f109])).

fof(f59,plain,
    ( spl5_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f94,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f61,f83])).

fof(f61,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f92,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f37,f90])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f88,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f36,f86])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f84,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f45,f82])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f76,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f72,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24])).

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

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f67,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f54])).

fof(f31,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (13406)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (13403)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (13405)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (13416)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (13418)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (13407)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (13410)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (13413)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (13412)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (13402)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (13404)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (13401)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (13419)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (13417)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (13409)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (13411)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.51  % (13406)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f3067,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f76,f84,f88,f92,f112,f116,f120,f124,f132,f136,f146,f165,f202,f313,f383,f417,f453,f648,f766,f1504,f1820,f1935,f3031,f3064])).
% 0.20/0.51  fof(f3064,plain,(
% 0.20/0.51    ~spl5_5 | ~spl5_8 | ~spl5_21 | ~spl5_45 | spl5_60 | spl5_81 | ~spl5_97 | ~spl5_101 | ~spl5_137),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f3063])).
% 0.20/0.51  fof(f3063,plain,(
% 0.20/0.51    $false | (~spl5_5 | ~spl5_8 | ~spl5_21 | ~spl5_45 | spl5_60 | spl5_81 | ~spl5_97 | ~spl5_101 | ~spl5_137)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1950,f3062])).
% 0.20/0.51  fof(f3062,plain,(
% 0.20/0.51    ~r1_tarski(sK1,k4_xboole_0(sK1,sK0)) | (~spl5_5 | ~spl5_8 | spl5_81 | ~spl5_97 | ~spl5_137)),
% 0.20/0.51    inference(forward_demodulation,[],[f3044,f1823])).
% 0.20/0.51  fof(f1823,plain,(
% 0.20/0.51    ( ! [X2] : (k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k2_xboole_0(X2,sK2))) ) | (~spl5_8 | ~spl5_97)),
% 0.20/0.51    inference(superposition,[],[f1819,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl5_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl5_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.51  fof(f1819,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0)) ) | ~spl5_97),
% 0.20/0.51    inference(avatar_component_clause,[],[f1818])).
% 0.20/0.51  fof(f1818,plain,(
% 0.20/0.51    spl5_97 <=> ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 0.20/0.51  fof(f3044,plain,(
% 0.20/0.51    ~r1_tarski(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) | (~spl5_5 | spl5_81 | ~spl5_137)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f1503,f75,f3030])).
% 0.20/0.51  fof(f3030,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~r1_tarski(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3)) ) | ~spl5_137),
% 0.20/0.51    inference(avatar_component_clause,[],[f3029])).
% 0.20/0.51  fof(f3029,plain,(
% 0.20/0.51    spl5_137 <=> ! [X3,X2] : (X2 = X3 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,X3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl5_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl5_5 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.51  fof(f1503,plain,(
% 0.20/0.51    sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | spl5_81),
% 0.20/0.51    inference(avatar_component_clause,[],[f1501])).
% 0.20/0.51  fof(f1501,plain,(
% 0.20/0.51    spl5_81 <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 0.20/0.51  fof(f1950,plain,(
% 0.20/0.51    r1_tarski(sK1,k4_xboole_0(sK1,sK0)) | (~spl5_21 | ~spl5_45 | spl5_60 | ~spl5_101)),
% 0.20/0.51    inference(forward_demodulation,[],[f1944,f948])).
% 0.20/0.51  fof(f948,plain,(
% 0.20/0.51    sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) | (~spl5_21 | spl5_60)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f765,f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) ) | ~spl5_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f144])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    spl5_21 <=> ! [X1,X0] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.51  fof(f765,plain,(
% 0.20/0.51    ~r2_hidden(sK3,sK1) | spl5_60),
% 0.20/0.51    inference(avatar_component_clause,[],[f763])).
% 0.20/0.51  fof(f763,plain,(
% 0.20/0.51    spl5_60 <=> r2_hidden(sK3,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.20/0.51  fof(f1944,plain,(
% 0.20/0.51    r1_tarski(k4_xboole_0(sK1,k1_tarski(sK3)),k4_xboole_0(sK1,sK0)) | (~spl5_45 | ~spl5_101)),
% 0.20/0.51    inference(superposition,[],[f1934,f416])).
% 0.20/0.51  fof(f416,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) ) | ~spl5_45),
% 0.20/0.51    inference(avatar_component_clause,[],[f415])).
% 0.20/0.51  fof(f415,plain,(
% 0.20/0.51    spl5_45 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.20/0.51  fof(f1934,plain,(
% 0.20/0.51    ( ! [X12] : (r1_tarski(k4_xboole_0(X12,k1_tarski(sK3)),k4_xboole_0(X12,k3_xboole_0(sK0,sK1)))) ) | ~spl5_101),
% 0.20/0.51    inference(avatar_component_clause,[],[f1933])).
% 0.20/0.51  fof(f1933,plain,(
% 0.20/0.51    spl5_101 <=> ! [X12] : r1_tarski(k4_xboole_0(X12,k1_tarski(sK3)),k4_xboole_0(X12,k3_xboole_0(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).
% 0.20/0.51  fof(f3031,plain,(
% 0.20/0.51    spl5_137 | ~spl5_14 | ~spl5_43),
% 0.20/0.51    inference(avatar_split_clause,[],[f388,f381,f114,f3029])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl5_14 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.51  fof(f381,plain,(
% 0.20/0.51    spl5_43 <=> ! [X3,X2] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.20/0.51  fof(f388,plain,(
% 0.20/0.51    ( ! [X2,X3] : (X2 = X3 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,X3)) ) | (~spl5_14 | ~spl5_43)),
% 0.20/0.51    inference(superposition,[],[f382,f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl5_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f114])).
% 0.20/0.51  fof(f382,plain,(
% 0.20/0.51    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) ) | ~spl5_43),
% 0.20/0.51    inference(avatar_component_clause,[],[f381])).
% 0.20/0.51  fof(f1935,plain,(
% 0.20/0.51    spl5_101 | ~spl5_34 | ~spl5_47),
% 0.20/0.51    inference(avatar_split_clause,[],[f460,f451,f310,f1933])).
% 0.20/0.51  fof(f310,plain,(
% 0.20/0.51    spl5_34 <=> k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.20/0.51  fof(f451,plain,(
% 0.20/0.51    spl5_47 <=> ! [X9,X11,X10] : r1_tarski(k4_xboole_0(X9,k2_xboole_0(X10,X11)),k4_xboole_0(X9,X10))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.20/0.51  fof(f460,plain,(
% 0.20/0.51    ( ! [X12] : (r1_tarski(k4_xboole_0(X12,k1_tarski(sK3)),k4_xboole_0(X12,k3_xboole_0(sK0,sK1)))) ) | (~spl5_34 | ~spl5_47)),
% 0.20/0.51    inference(superposition,[],[f452,f312])).
% 0.20/0.51  fof(f312,plain,(
% 0.20/0.51    k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl5_34),
% 0.20/0.51    inference(avatar_component_clause,[],[f310])).
% 0.20/0.51  fof(f452,plain,(
% 0.20/0.51    ( ! [X10,X11,X9] : (r1_tarski(k4_xboole_0(X9,k2_xboole_0(X10,X11)),k4_xboole_0(X9,X10))) ) | ~spl5_47),
% 0.20/0.51    inference(avatar_component_clause,[],[f451])).
% 0.20/0.51  fof(f1820,plain,(
% 0.20/0.51    spl5_97 | ~spl5_13 | ~spl5_57),
% 0.20/0.51    inference(avatar_split_clause,[],[f650,f646,f109,f1818])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl5_13 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.51  fof(f646,plain,(
% 0.20/0.51    spl5_57 <=> ! [X1,X0,X2] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 0.20/0.51  fof(f650,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0)) ) | (~spl5_13 | ~spl5_57)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f111,f647])).
% 0.20/0.51  fof(f647,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) ) | ~spl5_57),
% 0.20/0.51    inference(avatar_component_clause,[],[f646])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    r1_xboole_0(sK1,sK2) | ~spl5_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f109])).
% 0.20/0.51  fof(f1504,plain,(
% 0.20/0.51    ~spl5_81 | ~spl5_16 | spl5_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f240,f162,f122,f1501])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl5_16 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    spl5_22 <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | (~spl5_16 | spl5_22)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f164,f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl5_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f122])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | spl5_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f162])).
% 0.20/0.51  fof(f766,plain,(
% 0.20/0.51    ~spl5_60 | ~spl5_1 | ~spl5_13 | ~spl5_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f187,f134,f109,f54,f763])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl5_1 <=> r2_hidden(sK3,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl5_19 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    ~r2_hidden(sK3,sK1) | (~spl5_1 | ~spl5_13 | ~spl5_19)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f111,f56,f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) ) | ~spl5_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f134])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    r2_hidden(sK3,sK2) | ~spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f648,plain,(
% 0.20/0.51    spl5_57 | ~spl5_15 | ~spl5_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f212,f200,f118,f646])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl5_15 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    spl5_24 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.51  fof(f212,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) ) | (~spl5_15 | ~spl5_24)),
% 0.20/0.51    inference(superposition,[],[f201,f119])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl5_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f118])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl5_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f200])).
% 0.20/0.51  fof(f453,plain,(
% 0.20/0.51    spl5_47 | ~spl5_5 | ~spl5_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f224,f200,f74,f451])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    ( ! [X10,X11,X9] : (r1_tarski(k4_xboole_0(X9,k2_xboole_0(X10,X11)),k4_xboole_0(X9,X10))) ) | (~spl5_5 | ~spl5_24)),
% 0.20/0.51    inference(superposition,[],[f75,f201])).
% 0.20/0.51  fof(f417,plain,(
% 0.20/0.51    spl5_45 | ~spl5_9 | ~spl5_18),
% 0.20/0.51    inference(avatar_split_clause,[],[f177,f130,f90,f415])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl5_9 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    spl5_18 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) ) | (~spl5_9 | ~spl5_18)),
% 0.20/0.51    inference(superposition,[],[f131,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl5_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f90])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl5_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f130])).
% 0.20/0.51  fof(f383,plain,(
% 0.20/0.51    spl5_43 | ~spl5_8 | ~spl5_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f151,f114,f86,f381])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) ) | (~spl5_8 | ~spl5_14)),
% 0.20/0.51    inference(superposition,[],[f115,f87])).
% 0.20/0.51  fof(f313,plain,(
% 0.20/0.51    spl5_34 | ~spl5_4 | ~spl5_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f149,f114,f69,f310])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl5_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | (~spl5_4 | ~spl5_14)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f71,f115])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f69])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    spl5_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f51,f200])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ~spl5_22 | spl5_3 | ~spl5_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f93,f82,f64,f162])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl5_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl5_7 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | (spl5_3 | ~spl5_7)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f66,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl5_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f64])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    spl5_21),
% 0.20/0.51    inference(avatar_split_clause,[],[f49,f144])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    spl5_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f43,f134])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    spl5_18),
% 0.20/0.51    inference(avatar_split_clause,[],[f40,f130])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl5_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f47,f122])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    spl5_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f46,f118])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    spl5_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f44,f114])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    spl5_13 | ~spl5_2 | ~spl5_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f94,f82,f59,f109])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl5_2 <=> r1_xboole_0(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    r1_xboole_0(sK1,sK2) | (~spl5_2 | ~spl5_7)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f61,f83])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    r1_xboole_0(sK2,sK1) | ~spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl5_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f37,f90])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl5_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f36,f86])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    spl5_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f82])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    spl5_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f35,f74])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f69])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.20/0.51    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.51    inference(negated_conjecture,[],[f16])).
% 0.20/0.51  fof(f16,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f33,f64])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f32,f59])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    r1_xboole_0(sK2,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f31,f54])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    r2_hidden(sK3,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (13406)------------------------------
% 0.20/0.51  % (13406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13406)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (13406)Memory used [KB]: 8571
% 0.20/0.51  % (13406)Time elapsed: 0.074 s
% 0.20/0.51  % (13406)------------------------------
% 0.20/0.51  % (13406)------------------------------
% 0.20/0.52  % (13400)Success in time 0.156 s
%------------------------------------------------------------------------------
