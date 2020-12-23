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
% DateTime   : Thu Dec  3 12:51:34 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 239 expanded)
%              Number of leaves         :   43 ( 111 expanded)
%              Depth                    :    6
%              Number of atoms          :  420 ( 658 expanded)
%              Number of equality atoms :   48 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f96,f104,f116,f120,f136,f144,f152,f169,f173,f183,f246,f250,f285,f296,f302,f327,f343,f442,f526,f544,f567,f573,f633,f1020,f1031,f1050])).

fof(f1050,plain,
    ( ~ spl4_5
    | spl4_49
    | ~ spl4_116 ),
    inference(avatar_contradiction_clause,[],[f1049])).

fof(f1049,plain,
    ( $false
    | ~ spl4_5
    | spl4_49
    | ~ spl4_116 ),
    inference(subsumption_resolution,[],[f1032,f91])).

fof(f91,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1032,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | spl4_49
    | ~ spl4_116 ),
    inference(backward_demodulation,[],[f342,f1016])).

fof(f1016,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_116 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f1015,plain,
    ( spl4_116
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f342,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl4_49 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl4_49
  <=> r1_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f1031,plain,
    ( ~ spl4_2
    | ~ spl4_8
    | spl4_117 ),
    inference(avatar_contradiction_clause,[],[f1030])).

fof(f1030,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_8
    | spl4_117 ),
    inference(subsumption_resolution,[],[f1028,f79])).

fof(f79,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1028,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl4_8
    | spl4_117 ),
    inference(resolution,[],[f1019,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1019,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl4_117 ),
    inference(avatar_component_clause,[],[f1018])).

fof(f1018,plain,
    ( spl4_117
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).

fof(f1020,plain,
    ( spl4_116
    | ~ spl4_117
    | ~ spl4_23
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f658,f631,f167,f1018,f1015])).

fof(f167,plain,
    ( spl4_23
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f631,plain,
    ( spl4_81
  <=> k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f658,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_23
    | ~ spl4_81 ),
    inference(trivial_inequality_removal,[],[f651])).

fof(f651,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_23
    | ~ spl4_81 ),
    inference(superposition,[],[f168,f632])).

fof(f632,plain,
    ( k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f631])).

fof(f168,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f167])).

fof(f633,plain,
    ( spl4_81
    | ~ spl4_19
    | ~ spl4_42
    | ~ spl4_72
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f593,f571,f514,f294,f150,f631])).

fof(f150,plain,
    ( spl4_19
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f294,plain,
    ( spl4_42
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f514,plain,
    ( spl4_72
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f571,plain,
    ( spl4_76
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,k3_xboole_0(X0,X0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f593,plain,
    ( k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl4_19
    | ~ spl4_42
    | ~ spl4_72
    | ~ spl4_76 ),
    inference(subsumption_resolution,[],[f585,f540])).

fof(f540,plain,
    ( ! [X2] : r1_xboole_0(k1_xboole_0,X2)
    | ~ spl4_19
    | ~ spl4_72 ),
    inference(resolution,[],[f515,f151])).

fof(f151,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f150])).

fof(f515,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f514])).

fof(f585,plain,
    ( k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(k3_xboole_0(sK0,sK1))))
    | ~ spl4_42
    | ~ spl4_76 ),
    inference(resolution,[],[f572,f295])).

fof(f295,plain,
    ( ! [X0] :
        ( r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),X0)
        | ~ r1_xboole_0(k1_xboole_0,X0) )
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f294])).

fof(f572,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k3_xboole_0(X0,X0))
        | k1_xboole_0 = X0 )
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f571])).

fof(f573,plain,
    ( spl4_76
    | ~ spl4_6
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f332,f325,f94,f571])).

fof(f94,plain,
    ( spl4_6
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_xboole_0(X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f325,plain,
    ( spl4_46
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k3_xboole_0(X0,X0))
        | k1_xboole_0 = X0 )
    | ~ spl4_6
    | ~ spl4_46 ),
    inference(resolution,[],[f326,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f326,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,k3_xboole_0(X0,X1)) )
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f325])).

fof(f567,plain,
    ( ~ spl4_21
    | spl4_72
    | ~ spl4_5
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f443,f440,f90,f514,f159])).

fof(f159,plain,
    ( spl4_21
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f440,plain,
    ( spl4_60
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,X1)
        | ~ r1_xboole_0(k1_tarski(k4_tarski(sK2(X0,X1),sK3(X0,X1))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f443,plain,
    ( ! [X0] :
        ( r1_tarski(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_5
    | ~ spl4_60 ),
    inference(resolution,[],[f441,f91])).

fof(f441,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(k4_tarski(sK2(X0,X1),sK3(X0,X1))),X0)
        | r1_tarski(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f440])).

fof(f544,plain,
    ( spl4_20
    | spl4_21
    | ~ spl4_8
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f308,f300,f102,f159,f156])).

fof(f156,plain,
    ( spl4_20
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f300,plain,
    ( spl4_43
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f308,plain,
    ( ! [X3] :
        ( v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X3) )
    | ~ spl4_8
    | ~ spl4_43 ),
    inference(superposition,[],[f103,f301])).

fof(f301,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f300])).

fof(f526,plain,
    ( ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(resolution,[],[f157,f79])).

fof(f157,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f156])).

fof(f442,plain,
    ( spl4_60
    | ~ spl4_12
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f286,f248,f118,f440])).

fof(f118,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f248,plain,
    ( spl4_35
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,X1)
        | ~ r1_xboole_0(k1_tarski(k4_tarski(sK2(X0,X1),sK3(X0,X1))),X0) )
    | ~ spl4_12
    | ~ spl4_35 ),
    inference(resolution,[],[f249,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_xboole_0(k1_tarski(X0),X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        | ~ v1_relat_1(X0)
        | r1_tarski(X0,X1) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f248])).

fof(f343,plain,
    ( ~ spl4_49
    | spl4_3
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f334,f325,f82,f341])).

fof(f82,plain,
    ( spl4_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f334,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl4_3
    | ~ spl4_46 ),
    inference(resolution,[],[f326,f83])).

fof(f83,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f327,plain,
    ( spl4_46
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f174,f134,f114,f325])).

fof(f114,plain,
    ( spl4_11
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f134,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,k3_xboole_0(X0,X1)) )
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(superposition,[],[f115,f135])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f115,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f302,plain,
    ( spl4_43
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f177,f142,f90,f300])).

fof(f142,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f177,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(resolution,[],[f143,f91])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f142])).

fof(f296,plain,
    ( spl4_42
    | ~ spl4_24
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f289,f283,f171,f294])).

fof(f171,plain,
    ( spl4_24
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f283,plain,
    ( spl4_41
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),X0) )
    | ~ spl4_24
    | ~ spl4_41 ),
    inference(resolution,[],[f284,f172])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f171])).

fof(f284,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f283])).

fof(f285,plain,
    ( spl4_41
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_25
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f281,f244,f181,f78,f74,f283])).

fof(f74,plain,
    ( spl4_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f181,plain,
    ( spl4_25
  <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f244,plain,
    ( spl4_34
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f281,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_25
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f280,f79])).

fof(f280,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ spl4_1
    | ~ spl4_25
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f279,f75])).

fof(f75,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f279,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl4_25
    | ~ spl4_34 ),
    inference(superposition,[],[f245,f182])).

fof(f182,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f181])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f244])).

fof(f250,plain,(
    spl4_35 ),
    inference(avatar_split_clause,[],[f55,f248])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f246,plain,(
    spl4_34 ),
    inference(avatar_split_clause,[],[f51,f244])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f183,plain,
    ( spl4_25
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f176,f142,f86,f181])).

fof(f86,plain,
    ( spl4_4
  <=> r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f176,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(resolution,[],[f143,f87])).

fof(f87,plain,
    ( r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f173,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f71,f171])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f169,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f50,f167])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f152,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f70,f150])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f144,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f67,f142])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f136,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f65,f134])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f120,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f68,f118])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f116,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f57,f114])).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f104,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f59,f102])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f96,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f92,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f45,f90])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f88,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f86])).

fof(f42,plain,(
    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).

fof(f84,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f43,f82])).

fof(f43,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f78])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f41,f74])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (11493)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (11501)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (11485)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (11484)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (11486)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (11501)Refutation not found, incomplete strategy% (11501)------------------------------
% 0.20/0.51  % (11501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11501)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11501)Memory used [KB]: 10618
% 0.20/0.51  % (11501)Time elapsed: 0.090 s
% 0.20/0.51  % (11501)------------------------------
% 0.20/0.51  % (11501)------------------------------
% 0.20/0.51  % (11489)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (11488)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  % (11491)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (11494)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.52  % (11497)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.52  % (11500)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.53  % (11481)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (11495)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.53  % (11492)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.31/0.53  % (11496)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.31/0.53  % (11483)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.31/0.54  % (11491)Refutation not found, incomplete strategy% (11491)------------------------------
% 1.31/0.54  % (11491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (11491)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (11491)Memory used [KB]: 6012
% 1.31/0.54  % (11491)Time elapsed: 0.089 s
% 1.31/0.54  % (11491)------------------------------
% 1.31/0.54  % (11491)------------------------------
% 1.31/0.54  % (11482)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (11487)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.31/0.54  % (11482)Refutation not found, incomplete strategy% (11482)------------------------------
% 1.31/0.54  % (11482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (11482)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (11482)Memory used [KB]: 10618
% 1.31/0.54  % (11482)Time elapsed: 0.101 s
% 1.31/0.54  % (11482)------------------------------
% 1.31/0.54  % (11482)------------------------------
% 1.31/0.54  % (11499)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.31/0.54  % (11490)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.31/0.55  % (11498)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.50/0.58  % (11490)Refutation found. Thanks to Tanya!
% 1.50/0.58  % SZS status Theorem for theBenchmark
% 1.50/0.60  % SZS output start Proof for theBenchmark
% 1.50/0.60  fof(f1131,plain,(
% 1.50/0.60    $false),
% 1.50/0.60    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f96,f104,f116,f120,f136,f144,f152,f169,f173,f183,f246,f250,f285,f296,f302,f327,f343,f442,f526,f544,f567,f573,f633,f1020,f1031,f1050])).
% 1.50/0.60  fof(f1050,plain,(
% 1.50/0.60    ~spl4_5 | spl4_49 | ~spl4_116),
% 1.50/0.60    inference(avatar_contradiction_clause,[],[f1049])).
% 1.50/0.60  fof(f1049,plain,(
% 1.50/0.60    $false | (~spl4_5 | spl4_49 | ~spl4_116)),
% 1.50/0.60    inference(subsumption_resolution,[],[f1032,f91])).
% 1.50/0.60  fof(f91,plain,(
% 1.50/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_5),
% 1.50/0.60    inference(avatar_component_clause,[],[f90])).
% 1.50/0.60  fof(f90,plain,(
% 1.50/0.60    spl4_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.50/0.60  fof(f1032,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,k1_xboole_0) | (spl4_49 | ~spl4_116)),
% 1.50/0.60    inference(backward_demodulation,[],[f342,f1016])).
% 1.50/0.60  fof(f1016,plain,(
% 1.50/0.60    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_116),
% 1.50/0.60    inference(avatar_component_clause,[],[f1015])).
% 1.50/0.60  fof(f1015,plain,(
% 1.50/0.60    spl4_116 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).
% 1.50/0.60  fof(f342,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl4_49),
% 1.50/0.60    inference(avatar_component_clause,[],[f341])).
% 1.50/0.60  fof(f341,plain,(
% 1.50/0.60    spl4_49 <=> r1_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.50/0.60  fof(f1031,plain,(
% 1.50/0.60    ~spl4_2 | ~spl4_8 | spl4_117),
% 1.50/0.60    inference(avatar_contradiction_clause,[],[f1030])).
% 1.50/0.60  fof(f1030,plain,(
% 1.50/0.60    $false | (~spl4_2 | ~spl4_8 | spl4_117)),
% 1.50/0.60    inference(subsumption_resolution,[],[f1028,f79])).
% 1.50/0.60  fof(f79,plain,(
% 1.50/0.60    v1_relat_1(sK0) | ~spl4_2),
% 1.50/0.60    inference(avatar_component_clause,[],[f78])).
% 1.50/0.60  fof(f78,plain,(
% 1.50/0.60    spl4_2 <=> v1_relat_1(sK0)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.50/0.60  fof(f1028,plain,(
% 1.50/0.60    ~v1_relat_1(sK0) | (~spl4_8 | spl4_117)),
% 1.50/0.60    inference(resolution,[],[f1019,f103])).
% 1.50/0.60  fof(f103,plain,(
% 1.50/0.60    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl4_8),
% 1.50/0.60    inference(avatar_component_clause,[],[f102])).
% 1.50/0.60  fof(f102,plain,(
% 1.50/0.60    spl4_8 <=> ! [X1,X0] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.50/0.60  fof(f1019,plain,(
% 1.50/0.60    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl4_117),
% 1.50/0.60    inference(avatar_component_clause,[],[f1018])).
% 1.50/0.60  fof(f1018,plain,(
% 1.50/0.60    spl4_117 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).
% 1.50/0.60  fof(f1020,plain,(
% 1.50/0.60    spl4_116 | ~spl4_117 | ~spl4_23 | ~spl4_81),
% 1.50/0.60    inference(avatar_split_clause,[],[f658,f631,f167,f1018,f1015])).
% 1.50/0.60  fof(f167,plain,(
% 1.50/0.60    spl4_23 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.50/0.60  fof(f631,plain,(
% 1.50/0.60    spl4_81 <=> k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 1.50/0.60  fof(f658,plain,(
% 1.50/0.60    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl4_23 | ~spl4_81)),
% 1.50/0.60    inference(trivial_inequality_removal,[],[f651])).
% 1.50/0.60  fof(f651,plain,(
% 1.50/0.60    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl4_23 | ~spl4_81)),
% 1.50/0.60    inference(superposition,[],[f168,f632])).
% 1.50/0.60  fof(f632,plain,(
% 1.50/0.60    k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1)) | ~spl4_81),
% 1.50/0.60    inference(avatar_component_clause,[],[f631])).
% 1.50/0.60  fof(f168,plain,(
% 1.50/0.60    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) ) | ~spl4_23),
% 1.50/0.60    inference(avatar_component_clause,[],[f167])).
% 1.50/0.60  fof(f633,plain,(
% 1.50/0.60    spl4_81 | ~spl4_19 | ~spl4_42 | ~spl4_72 | ~spl4_76),
% 1.50/0.60    inference(avatar_split_clause,[],[f593,f571,f514,f294,f150,f631])).
% 1.50/0.60  fof(f150,plain,(
% 1.50/0.60    spl4_19 <=> ! [X1,X0,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.50/0.60  fof(f294,plain,(
% 1.50/0.60    spl4_42 <=> ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),X0))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.50/0.60  fof(f514,plain,(
% 1.50/0.60    spl4_72 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 1.50/0.60  fof(f571,plain,(
% 1.50/0.60    spl4_76 <=> ! [X0] : (~r1_xboole_0(X0,k3_xboole_0(X0,X0)) | k1_xboole_0 = X0)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 1.50/0.60  fof(f593,plain,(
% 1.50/0.60    k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1)) | (~spl4_19 | ~spl4_42 | ~spl4_72 | ~spl4_76)),
% 1.50/0.60    inference(subsumption_resolution,[],[f585,f540])).
% 1.50/0.60  fof(f540,plain,(
% 1.50/0.60    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) ) | (~spl4_19 | ~spl4_72)),
% 1.50/0.60    inference(resolution,[],[f515,f151])).
% 1.50/0.60  fof(f151,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) ) | ~spl4_19),
% 1.50/0.60    inference(avatar_component_clause,[],[f150])).
% 1.50/0.60  fof(f515,plain,(
% 1.50/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_72),
% 1.50/0.60    inference(avatar_component_clause,[],[f514])).
% 1.50/0.60  fof(f585,plain,(
% 1.50/0.60    k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(k1_xboole_0,k3_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(k3_xboole_0(sK0,sK1)))) | (~spl4_42 | ~spl4_76)),
% 1.50/0.60    inference(resolution,[],[f572,f295])).
% 1.50/0.60  fof(f295,plain,(
% 1.50/0.60    ( ! [X0] : (r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),X0) | ~r1_xboole_0(k1_xboole_0,X0)) ) | ~spl4_42),
% 1.50/0.60    inference(avatar_component_clause,[],[f294])).
% 1.50/0.60  fof(f572,plain,(
% 1.50/0.60    ( ! [X0] : (~r1_xboole_0(X0,k3_xboole_0(X0,X0)) | k1_xboole_0 = X0) ) | ~spl4_76),
% 1.50/0.60    inference(avatar_component_clause,[],[f571])).
% 1.50/0.60  fof(f573,plain,(
% 1.50/0.60    spl4_76 | ~spl4_6 | ~spl4_46),
% 1.50/0.60    inference(avatar_split_clause,[],[f332,f325,f94,f571])).
% 1.50/0.60  fof(f94,plain,(
% 1.50/0.60    spl4_6 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_xboole_0(X0,X0))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.50/0.60  fof(f325,plain,(
% 1.50/0.60    spl4_46 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,k3_xboole_0(X0,X1)))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.50/0.60  fof(f332,plain,(
% 1.50/0.60    ( ! [X0] : (~r1_xboole_0(X0,k3_xboole_0(X0,X0)) | k1_xboole_0 = X0) ) | (~spl4_6 | ~spl4_46)),
% 1.50/0.60    inference(resolution,[],[f326,f95])).
% 1.50/0.60  fof(f95,plain,(
% 1.50/0.60    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) ) | ~spl4_6),
% 1.50/0.60    inference(avatar_component_clause,[],[f94])).
% 1.50/0.60  fof(f326,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl4_46),
% 1.50/0.60    inference(avatar_component_clause,[],[f325])).
% 1.50/0.60  fof(f567,plain,(
% 1.50/0.60    ~spl4_21 | spl4_72 | ~spl4_5 | ~spl4_60),
% 1.50/0.60    inference(avatar_split_clause,[],[f443,f440,f90,f514,f159])).
% 1.50/0.60  fof(f159,plain,(
% 1.50/0.60    spl4_21 <=> v1_relat_1(k1_xboole_0)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.50/0.60  fof(f440,plain,(
% 1.50/0.60    spl4_60 <=> ! [X1,X0] : (~v1_relat_1(X0) | r1_tarski(X0,X1) | ~r1_xboole_0(k1_tarski(k4_tarski(sK2(X0,X1),sK3(X0,X1))),X0))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 1.50/0.60  fof(f443,plain,(
% 1.50/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_5 | ~spl4_60)),
% 1.50/0.60    inference(resolution,[],[f441,f91])).
% 1.50/0.60  fof(f441,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(k4_tarski(sK2(X0,X1),sK3(X0,X1))),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) ) | ~spl4_60),
% 1.50/0.60    inference(avatar_component_clause,[],[f440])).
% 1.50/0.60  fof(f544,plain,(
% 1.50/0.60    spl4_20 | spl4_21 | ~spl4_8 | ~spl4_43),
% 1.50/0.60    inference(avatar_split_clause,[],[f308,f300,f102,f159,f156])).
% 1.50/0.60  fof(f156,plain,(
% 1.50/0.60    spl4_20 <=> ! [X0] : ~v1_relat_1(X0)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.50/0.60  fof(f300,plain,(
% 1.50/0.60    spl4_43 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.50/0.60  fof(f308,plain,(
% 1.50/0.60    ( ! [X3] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X3)) ) | (~spl4_8 | ~spl4_43)),
% 1.50/0.60    inference(superposition,[],[f103,f301])).
% 1.50/0.60  fof(f301,plain,(
% 1.50/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl4_43),
% 1.50/0.60    inference(avatar_component_clause,[],[f300])).
% 1.50/0.60  fof(f526,plain,(
% 1.50/0.60    ~spl4_2 | ~spl4_20),
% 1.50/0.60    inference(avatar_contradiction_clause,[],[f523])).
% 1.50/0.60  fof(f523,plain,(
% 1.50/0.60    $false | (~spl4_2 | ~spl4_20)),
% 1.50/0.60    inference(resolution,[],[f157,f79])).
% 1.50/0.60  fof(f157,plain,(
% 1.50/0.60    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl4_20),
% 1.50/0.60    inference(avatar_component_clause,[],[f156])).
% 1.50/0.60  fof(f442,plain,(
% 1.50/0.60    spl4_60 | ~spl4_12 | ~spl4_35),
% 1.50/0.60    inference(avatar_split_clause,[],[f286,f248,f118,f440])).
% 1.50/0.60  fof(f118,plain,(
% 1.50/0.60    spl4_12 <=> ! [X1,X0] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.50/0.60  fof(f248,plain,(
% 1.50/0.60    spl4_35 <=> ! [X1,X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r1_tarski(X0,X1))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.50/0.60  fof(f286,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(X0,X1) | ~r1_xboole_0(k1_tarski(k4_tarski(sK2(X0,X1),sK3(X0,X1))),X0)) ) | (~spl4_12 | ~spl4_35)),
% 1.50/0.60    inference(resolution,[],[f249,f119])).
% 1.50/0.60  fof(f119,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) ) | ~spl4_12),
% 1.50/0.60    inference(avatar_component_clause,[],[f118])).
% 1.50/0.60  fof(f249,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) ) | ~spl4_35),
% 1.50/0.60    inference(avatar_component_clause,[],[f248])).
% 1.50/0.60  fof(f343,plain,(
% 1.50/0.60    ~spl4_49 | spl4_3 | ~spl4_46),
% 1.50/0.60    inference(avatar_split_clause,[],[f334,f325,f82,f341])).
% 1.50/0.60  fof(f82,plain,(
% 1.50/0.60    spl4_3 <=> r1_xboole_0(sK0,sK1)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.50/0.60  fof(f334,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | (spl4_3 | ~spl4_46)),
% 1.50/0.60    inference(resolution,[],[f326,f83])).
% 1.50/0.60  fof(f83,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,sK1) | spl4_3),
% 1.50/0.60    inference(avatar_component_clause,[],[f82])).
% 1.50/0.60  fof(f327,plain,(
% 1.50/0.60    spl4_46 | ~spl4_11 | ~spl4_15),
% 1.50/0.60    inference(avatar_split_clause,[],[f174,f134,f114,f325])).
% 1.50/0.60  fof(f114,plain,(
% 1.50/0.60    spl4_11 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.50/0.60  fof(f134,plain,(
% 1.50/0.60    spl4_15 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.50/0.60  fof(f174,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,k3_xboole_0(X0,X1))) ) | (~spl4_11 | ~spl4_15)),
% 1.50/0.60    inference(superposition,[],[f115,f135])).
% 1.50/0.60  fof(f135,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl4_15),
% 1.50/0.60    inference(avatar_component_clause,[],[f134])).
% 1.50/0.60  fof(f115,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) ) | ~spl4_11),
% 1.50/0.60    inference(avatar_component_clause,[],[f114])).
% 1.50/0.60  fof(f302,plain,(
% 1.50/0.60    spl4_43 | ~spl4_5 | ~spl4_17),
% 1.50/0.60    inference(avatar_split_clause,[],[f177,f142,f90,f300])).
% 1.50/0.60  fof(f142,plain,(
% 1.50/0.60    spl4_17 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.50/0.60  fof(f177,plain,(
% 1.50/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl4_5 | ~spl4_17)),
% 1.50/0.60    inference(resolution,[],[f143,f91])).
% 1.50/0.60  fof(f143,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl4_17),
% 1.50/0.60    inference(avatar_component_clause,[],[f142])).
% 1.50/0.60  fof(f296,plain,(
% 1.50/0.60    spl4_42 | ~spl4_24 | ~spl4_41),
% 1.50/0.60    inference(avatar_split_clause,[],[f289,f283,f171,f294])).
% 1.50/0.60  fof(f171,plain,(
% 1.50/0.60    spl4_24 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.50/0.60  fof(f283,plain,(
% 1.50/0.60    spl4_41 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.50/0.60  fof(f289,plain,(
% 1.50/0.60    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(k2_relat_1(k3_xboole_0(sK0,sK1)),X0)) ) | (~spl4_24 | ~spl4_41)),
% 1.50/0.60    inference(resolution,[],[f284,f172])).
% 1.50/0.60  fof(f172,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl4_24),
% 1.50/0.60    inference(avatar_component_clause,[],[f171])).
% 1.50/0.60  fof(f284,plain,(
% 1.50/0.60    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl4_41),
% 1.50/0.60    inference(avatar_component_clause,[],[f283])).
% 1.50/0.60  fof(f285,plain,(
% 1.50/0.60    spl4_41 | ~spl4_1 | ~spl4_2 | ~spl4_25 | ~spl4_34),
% 1.50/0.60    inference(avatar_split_clause,[],[f281,f244,f181,f78,f74,f283])).
% 1.50/0.60  fof(f74,plain,(
% 1.50/0.60    spl4_1 <=> v1_relat_1(sK1)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.50/0.60  fof(f181,plain,(
% 1.50/0.60    spl4_25 <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.50/0.60  fof(f244,plain,(
% 1.50/0.60    spl4_34 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.50/0.60  fof(f281,plain,(
% 1.50/0.60    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | (~spl4_1 | ~spl4_2 | ~spl4_25 | ~spl4_34)),
% 1.50/0.60    inference(subsumption_resolution,[],[f280,f79])).
% 1.50/0.60  fof(f280,plain,(
% 1.50/0.60    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK0) | (~spl4_1 | ~spl4_25 | ~spl4_34)),
% 1.50/0.60    inference(subsumption_resolution,[],[f279,f75])).
% 1.50/0.60  fof(f75,plain,(
% 1.50/0.60    v1_relat_1(sK1) | ~spl4_1),
% 1.50/0.60    inference(avatar_component_clause,[],[f74])).
% 1.50/0.60  fof(f279,plain,(
% 1.50/0.60    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | (~spl4_25 | ~spl4_34)),
% 1.50/0.60    inference(superposition,[],[f245,f182])).
% 1.50/0.60  fof(f182,plain,(
% 1.50/0.60    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl4_25),
% 1.50/0.60    inference(avatar_component_clause,[],[f181])).
% 1.50/0.60  fof(f245,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl4_34),
% 1.50/0.60    inference(avatar_component_clause,[],[f244])).
% 1.50/0.60  fof(f250,plain,(
% 1.50/0.60    spl4_35),
% 1.50/0.60    inference(avatar_split_clause,[],[f55,f248])).
% 1.50/0.60  fof(f55,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f30])).
% 1.50/0.60  fof(f30,plain,(
% 1.50/0.60    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f10])).
% 1.50/0.60  fof(f10,axiom,(
% 1.50/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 1.50/0.60  fof(f246,plain,(
% 1.50/0.60    spl4_34),
% 1.50/0.60    inference(avatar_split_clause,[],[f51,f244])).
% 1.50/0.60  fof(f51,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f27])).
% 1.50/0.60  fof(f27,plain,(
% 1.50/0.60    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f17])).
% 1.50/0.60  fof(f17,axiom,(
% 1.50/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).
% 1.50/0.60  fof(f183,plain,(
% 1.50/0.60    spl4_25 | ~spl4_4 | ~spl4_17),
% 1.50/0.60    inference(avatar_split_clause,[],[f176,f142,f86,f181])).
% 1.50/0.60  fof(f86,plain,(
% 1.50/0.60    spl4_4 <=> r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.50/0.60  fof(f176,plain,(
% 1.50/0.60    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) | (~spl4_4 | ~spl4_17)),
% 1.50/0.60    inference(resolution,[],[f143,f87])).
% 1.50/0.60  fof(f87,plain,(
% 1.50/0.60    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl4_4),
% 1.50/0.60    inference(avatar_component_clause,[],[f86])).
% 1.50/0.60  fof(f173,plain,(
% 1.50/0.60    spl4_24),
% 1.50/0.60    inference(avatar_split_clause,[],[f71,f171])).
% 1.50/0.60  fof(f71,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f40])).
% 1.50/0.60  fof(f40,plain,(
% 1.50/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.50/0.60    inference(flattening,[],[f39])).
% 1.50/0.60  fof(f39,plain,(
% 1.50/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.50/0.60    inference(ennf_transformation,[],[f4])).
% 1.50/0.60  fof(f4,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.50/0.60  fof(f169,plain,(
% 1.50/0.60    spl4_23),
% 1.50/0.60    inference(avatar_split_clause,[],[f50,f167])).
% 1.50/0.60  fof(f50,plain,(
% 1.50/0.60    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.50/0.60    inference(cnf_transformation,[],[f26])).
% 1.50/0.60  fof(f26,plain,(
% 1.50/0.60    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.50/0.60    inference(flattening,[],[f25])).
% 1.50/0.60  fof(f25,plain,(
% 1.50/0.60    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f18])).
% 1.50/0.60  fof(f18,axiom,(
% 1.50/0.60    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.50/0.60  fof(f152,plain,(
% 1.50/0.60    spl4_19),
% 1.50/0.60    inference(avatar_split_clause,[],[f70,f150])).
% 1.50/0.60  fof(f70,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f38])).
% 1.50/0.60  fof(f38,plain,(
% 1.50/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.50/0.60    inference(ennf_transformation,[],[f3])).
% 1.50/0.60  fof(f3,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.50/0.60  fof(f144,plain,(
% 1.50/0.60    spl4_17),
% 1.50/0.60    inference(avatar_split_clause,[],[f67,f142])).
% 1.50/0.60  fof(f67,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f1])).
% 1.50/0.60  fof(f1,axiom,(
% 1.50/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.50/0.60  fof(f136,plain,(
% 1.50/0.60    spl4_15),
% 1.50/0.60    inference(avatar_split_clause,[],[f65,f134])).
% 1.50/0.60  fof(f65,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f7])).
% 1.50/0.60  fof(f7,axiom,(
% 1.50/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.50/0.60  fof(f120,plain,(
% 1.50/0.60    spl4_12),
% 1.50/0.60    inference(avatar_split_clause,[],[f68,f118])).
% 1.50/0.60  fof(f68,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f37])).
% 1.50/0.60  fof(f37,plain,(
% 1.50/0.60    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.50/0.60    inference(ennf_transformation,[],[f9])).
% 1.50/0.60  fof(f9,axiom,(
% 1.50/0.60    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.50/0.60  fof(f116,plain,(
% 1.50/0.60    spl4_11),
% 1.50/0.60    inference(avatar_split_clause,[],[f57,f114])).
% 1.50/0.60  fof(f57,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f8])).
% 1.50/0.60  fof(f8,axiom,(
% 1.50/0.60    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
% 1.50/0.60  fof(f104,plain,(
% 1.50/0.60    spl4_8),
% 1.50/0.60    inference(avatar_split_clause,[],[f59,f102])).
% 1.50/0.60  fof(f59,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f32])).
% 1.50/0.60  fof(f32,plain,(
% 1.50/0.60    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f12])).
% 1.50/0.60  fof(f12,axiom,(
% 1.50/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.50/0.60  fof(f96,plain,(
% 1.50/0.60    spl4_6),
% 1.50/0.60    inference(avatar_split_clause,[],[f46,f94])).
% 1.50/0.60  fof(f46,plain,(
% 1.50/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_xboole_0(X0,X0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f23])).
% 1.50/0.60  fof(f23,plain,(
% 1.50/0.60    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.50/0.60    inference(ennf_transformation,[],[f6])).
% 1.50/0.60  fof(f6,axiom,(
% 1.50/0.60    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.50/0.60  fof(f92,plain,(
% 1.50/0.60    spl4_5),
% 1.50/0.60    inference(avatar_split_clause,[],[f45,f90])).
% 1.50/0.60  fof(f45,plain,(
% 1.50/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f5])).
% 1.50/0.60  fof(f5,axiom,(
% 1.50/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.50/0.60  fof(f88,plain,(
% 1.50/0.60    spl4_4),
% 1.50/0.60    inference(avatar_split_clause,[],[f42,f86])).
% 1.50/0.60  fof(f42,plain,(
% 1.50/0.60    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.50/0.60    inference(cnf_transformation,[],[f22])).
% 1.50/0.60  fof(f22,plain,(
% 1.50/0.60    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.50/0.60    inference(flattening,[],[f21])).
% 1.50/0.60  fof(f21,plain,(
% 1.50/0.60    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f20])).
% 1.50/0.60  fof(f20,negated_conjecture,(
% 1.50/0.60    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 1.50/0.60    inference(negated_conjecture,[],[f19])).
% 1.50/0.60  fof(f19,conjecture,(
% 1.50/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).
% 1.50/0.60  fof(f84,plain,(
% 1.50/0.60    ~spl4_3),
% 1.50/0.60    inference(avatar_split_clause,[],[f43,f82])).
% 1.50/0.60  fof(f43,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,sK1)),
% 1.50/0.60    inference(cnf_transformation,[],[f22])).
% 1.50/0.60  fof(f80,plain,(
% 1.50/0.60    spl4_2),
% 1.50/0.60    inference(avatar_split_clause,[],[f44,f78])).
% 1.50/0.60  fof(f44,plain,(
% 1.50/0.60    v1_relat_1(sK0)),
% 1.50/0.60    inference(cnf_transformation,[],[f22])).
% 1.50/0.60  fof(f76,plain,(
% 1.50/0.60    spl4_1),
% 1.50/0.60    inference(avatar_split_clause,[],[f41,f74])).
% 1.50/0.60  fof(f41,plain,(
% 1.50/0.60    v1_relat_1(sK1)),
% 1.50/0.60    inference(cnf_transformation,[],[f22])).
% 1.50/0.60  % SZS output end Proof for theBenchmark
% 1.50/0.60  % (11490)------------------------------
% 1.50/0.60  % (11490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (11490)Termination reason: Refutation
% 1.50/0.60  
% 1.50/0.60  % (11490)Memory used [KB]: 11385
% 1.50/0.60  % (11490)Time elapsed: 0.168 s
% 1.50/0.60  % (11490)------------------------------
% 1.50/0.60  % (11490)------------------------------
% 1.50/0.60  % (11480)Success in time 0.237 s
%------------------------------------------------------------------------------
