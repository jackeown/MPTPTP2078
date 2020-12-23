%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t22_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:22 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 210 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  363 ( 718 expanded)
%              Number of equality atoms :   30 (  78 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f112,f125,f148,f214,f352,f1148,f1176,f1246,f1255,f1287,f1307])).

fof(f1307,plain,
    ( ~ spl11_4
    | ~ spl11_6
    | spl11_13
    | ~ spl11_160
    | ~ spl11_162 ),
    inference(avatar_contradiction_clause,[],[f1306])).

fof(f1306,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_13
    | ~ spl11_160
    | ~ spl11_162 ),
    inference(subsumption_resolution,[],[f1305,f1267])).

fof(f1267,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_13
    | ~ spl11_160 ),
    inference(subsumption_resolution,[],[f1266,f124])).

fof(f124,plain,
    ( k1_funct_1(k5_relat_1(sK2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(sK2,sK0))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl11_13
  <=> k1_funct_1(k5_relat_1(sK2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f1266,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | k1_funct_1(k5_relat_1(sK2,sK1),sK0) = k1_funct_1(sK1,k1_funct_1(sK2,sK0))
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_160 ),
    inference(subsumption_resolution,[],[f1265,f87])).

fof(f87,plain,
    ( v1_relat_1(sK1)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl11_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1265,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(sK2,sK1),sK0) = k1_funct_1(sK1,k1_funct_1(sK2,sK0))
    | ~ spl11_6
    | ~ spl11_160 ),
    inference(subsumption_resolution,[],[f1259,f91])).

fof(f91,plain,
    ( v1_funct_1(sK1)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl11_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f1259,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(sK2,sK1),sK0) = k1_funct_1(sK1,k1_funct_1(sK2,sK0))
    | ~ spl11_160 ),
    inference(resolution,[],[f1254,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',d4_funct_1)).

fof(f1254,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(k5_relat_1(sK2,sK1),sK0)),sK1)
    | ~ spl11_160 ),
    inference(avatar_component_clause,[],[f1253])).

fof(f1253,plain,
    ( spl11_160
  <=> r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(k5_relat_1(sK2,sK1),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_160])])).

fof(f1305,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ spl11_162 ),
    inference(resolution,[],[f1286,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',d4_relat_1)).

fof(f1286,plain,
    ( sP4(k1_funct_1(sK2,sK0),sK1)
    | ~ spl11_162 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f1285,plain,
    ( spl11_162
  <=> sP4(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_162])])).

fof(f1287,plain,
    ( spl11_162
    | ~ spl11_160 ),
    inference(avatar_split_clause,[],[f1261,f1253,f1285])).

fof(f1261,plain,
    ( sP4(k1_funct_1(sK2,sK0),sK1)
    | ~ spl11_160 ),
    inference(resolution,[],[f1254,f45])).

fof(f45,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f1255,plain,
    ( spl11_160
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_148
    | ~ spl11_150
    | ~ spl11_156 ),
    inference(avatar_split_clause,[],[f1247,f1244,f1174,f1146,f82,f78,f1253])).

fof(f78,plain,
    ( spl11_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f82,plain,
    ( spl11_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f1146,plain,
    ( spl11_148
  <=> r2_hidden(k4_tarski(sK0,sK9(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_148])])).

fof(f1174,plain,
    ( spl11_150
  <=> sP4(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_150])])).

fof(f1244,plain,
    ( spl11_156
  <=> r2_hidden(k4_tarski(sK9(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)),k1_funct_1(k5_relat_1(sK2,sK1),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_156])])).

fof(f1247,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(k5_relat_1(sK2,sK1),sK0)),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_148
    | ~ spl11_150
    | ~ spl11_156 ),
    inference(forward_demodulation,[],[f1245,f1190])).

fof(f1190,plain,
    ( k1_funct_1(sK2,sK0) = sK9(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_148
    | ~ spl11_150 ),
    inference(subsumption_resolution,[],[f1172,f1189])).

fof(f1189,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl11_150 ),
    inference(resolution,[],[f1175,f71])).

fof(f1175,plain,
    ( sP4(sK0,sK2)
    | ~ spl11_150 ),
    inference(avatar_component_clause,[],[f1174])).

fof(f1172,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | k1_funct_1(sK2,sK0) = sK9(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_148 ),
    inference(subsumption_resolution,[],[f1171,f79])).

fof(f79,plain,
    ( v1_relat_1(sK2)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f78])).

fof(f1171,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0) = sK9(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0))
    | ~ spl11_2
    | ~ spl11_148 ),
    inference(subsumption_resolution,[],[f1165,f83])).

fof(f83,plain,
    ( v1_funct_1(sK2)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f1165,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0) = sK9(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0))
    | ~ spl11_148 ),
    inference(resolution,[],[f1147,f59])).

fof(f1147,plain,
    ( r2_hidden(k4_tarski(sK0,sK9(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0))),sK2)
    | ~ spl11_148 ),
    inference(avatar_component_clause,[],[f1146])).

fof(f1245,plain,
    ( r2_hidden(k4_tarski(sK9(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)),k1_funct_1(k5_relat_1(sK2,sK1),sK0)),sK1)
    | ~ spl11_156 ),
    inference(avatar_component_clause,[],[f1244])).

fof(f1246,plain,
    ( spl11_156
    | ~ spl11_62 ),
    inference(avatar_split_clause,[],[f358,f350,f1244])).

fof(f350,plain,
    ( spl11_62
  <=> sP8(k1_funct_1(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_62])])).

fof(f358,plain,
    ( r2_hidden(k4_tarski(sK9(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)),k1_funct_1(k5_relat_1(sK2,sK1),sK0)),sK1)
    | ~ spl11_62 ),
    inference(resolution,[],[f351,f52])).

fof(f52,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(sK9(X0,X1,X3,X4),X4),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',d8_relat_1)).

fof(f351,plain,
    ( sP8(k1_funct_1(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ spl11_62 ),
    inference(avatar_component_clause,[],[f350])).

fof(f1176,plain,
    ( spl11_150
    | ~ spl11_148 ),
    inference(avatar_split_clause,[],[f1167,f1146,f1174])).

fof(f1167,plain,
    ( sP4(sK0,sK2)
    | ~ spl11_148 ),
    inference(resolution,[],[f1147,f45])).

fof(f1148,plain,
    ( spl11_148
    | ~ spl11_62 ),
    inference(avatar_split_clause,[],[f357,f350,f1146])).

fof(f357,plain,
    ( r2_hidden(k4_tarski(sK0,sK9(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0))),sK2)
    | ~ spl11_62 ),
    inference(resolution,[],[f351,f51])).

fof(f51,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,sK9(X0,X1,X3,X4)),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f352,plain,
    ( spl11_62
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f228,f212,f146,f86,f78,f350])).

fof(f146,plain,
    ( spl11_20
  <=> v1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f212,plain,
    ( spl11_30
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)),k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f228,plain,
    ( sP8(k1_funct_1(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f227,f79])).

fof(f227,plain,
    ( sP8(k1_funct_1(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f226,f147])).

fof(f147,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f146])).

fof(f226,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | sP8(k1_funct_1(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl11_4
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f219,f87])).

fof(f219,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | sP8(k1_funct_1(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl11_30 ),
    inference(resolution,[],[f213,f72])).

fof(f72,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | sP8(X4,X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | sP8(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f213,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)),k5_relat_1(sK2,sK1))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f212])).

fof(f214,plain,
    ( spl11_30
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f170,f110,f90,f86,f82,f78,f212])).

fof(f110,plain,
    ( spl11_8
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f170,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)),k5_relat_1(sK2,sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f134,f169])).

fof(f169,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f167,f87])).

fof(f167,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f99,f91])).

fof(f99,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v1_funct_1(k5_relat_1(sK2,X1)) )
    | ~ spl11_0
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f96,f79])).

fof(f96,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k5_relat_1(sK2,X1)) )
    | ~ spl11_2 ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',fc2_funct_1)).

fof(f134,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)),k5_relat_1(sK2,sK1))
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f113,f133])).

fof(f133,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl11_0
    | ~ spl11_4 ),
    inference(resolution,[],[f93,f87])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k5_relat_1(sK2,X0)) )
    | ~ spl11_0 ),
    inference(resolution,[],[f79,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',dt_k5_relat_1)).

fof(f113,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)),k5_relat_1(sK2,sK1))
    | ~ spl11_8 ),
    inference(resolution,[],[f111,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f148,plain,
    ( spl11_20
    | ~ spl11_0
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f133,f86,f78,f146])).

fof(f125,plain,(
    ~ spl11_13 ),
    inference(avatar_split_clause,[],[f40,f123])).

fof(f40,plain,(
    k1_funct_1(k5_relat_1(sK2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) != k1_funct_1(k5_relat_1(X2,X1),X0)
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) != k1_funct_1(k5_relat_1(X2,X1),X0)
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
             => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',t22_funct_1)).

fof(f112,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f39,f110])).

fof(f39,plain,(
    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f92,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f42,f90])).

fof(f42,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
