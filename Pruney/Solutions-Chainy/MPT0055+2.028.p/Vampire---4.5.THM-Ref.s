%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 149 expanded)
%              Number of leaves         :   25 (  74 expanded)
%              Depth                    :    6
%              Number of atoms          :  231 ( 370 expanded)
%              Number of equality atoms :   71 ( 125 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1366,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f49,f53,f69,f77,f81,f85,f139,f164,f178,f244,f264,f291,f730,f957,f1063,f1118,f1276,f1317])).

fof(f1317,plain,
    ( spl5_1
    | ~ spl5_67 ),
    inference(avatar_contradiction_clause,[],[f1277])).

fof(f1277,plain,
    ( $false
    | spl5_1
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f40,f1275])).

fof(f1275,plain,
    ( ! [X24,X25] : k3_xboole_0(X24,X25) = k4_xboole_0(X24,k4_xboole_0(X24,X25))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1274,plain,
    ( spl5_67
  <=> ! [X25,X24] : k3_xboole_0(X24,X25) = k4_xboole_0(X24,k4_xboole_0(X24,X25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f40,plain,
    ( k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_1
  <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1276,plain,
    ( spl5_67
    | ~ spl5_31
    | ~ spl5_59
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f1173,f1116,f955,f262,f1274])).

fof(f262,plain,
    ( spl5_31
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f955,plain,
    ( spl5_59
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f1116,plain,
    ( spl5_65
  <=> ! [X7,X6] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f1173,plain,
    ( ! [X24,X25] : k3_xboole_0(X24,X25) = k4_xboole_0(X24,k4_xboole_0(X24,X25))
    | ~ spl5_31
    | ~ spl5_59
    | ~ spl5_65 ),
    inference(forward_demodulation,[],[f1132,f956])).

fof(f956,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f955])).

fof(f1132,plain,
    ( ! [X24,X25] : k3_xboole_0(X24,X25) = k4_xboole_0(X24,k4_xboole_0(k4_xboole_0(X24,X25),k3_xboole_0(X24,X25)))
    | ~ spl5_31
    | ~ spl5_65 ),
    inference(superposition,[],[f1117,f263])).

fof(f263,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f262])).

fof(f1117,plain,
    ( ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f1116])).

fof(f1118,plain,
    ( spl5_65
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f1084,f1061,f728,f289,f1116])).

fof(f289,plain,
    ( spl5_32
  <=> ! [X7,X6] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f728,plain,
    ( spl5_52
  <=> ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f1061,plain,
    ( spl5_62
  <=> ! [X9,X11,X10] :
        ( k4_xboole_0(X9,X10) = X9
        | ~ r2_hidden(sK4(X9,X10,X9),k4_xboole_0(X11,X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f1084,plain,
    ( ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6
    | ~ spl5_32
    | ~ spl5_52
    | ~ spl5_62 ),
    inference(backward_demodulation,[],[f290,f1083])).

fof(f1083,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0
    | ~ spl5_52
    | ~ spl5_62 ),
    inference(duplicate_literal_removal,[],[f1068])).

fof(f1068,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0
        | k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 )
    | ~ spl5_52
    | ~ spl5_62 ),
    inference(resolution,[],[f1062,f729])).

fof(f729,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK4(X1,X2,X1),X2)
        | k4_xboole_0(X1,X2) = X1 )
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f728])).

fof(f1062,plain,
    ( ! [X10,X11,X9] :
        ( ~ r2_hidden(sK4(X9,X10,X9),k4_xboole_0(X11,X9))
        | k4_xboole_0(X9,X10) = X9 )
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f290,plain,
    ( ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f289])).

fof(f1063,plain,
    ( spl5_62
    | ~ spl5_8
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f249,f242,f67,f1061])).

fof(f67,plain,
    ( spl5_8
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f242,plain,
    ( spl5_29
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f249,plain,
    ( ! [X10,X11,X9] :
        ( k4_xboole_0(X9,X10) = X9
        | ~ r2_hidden(sK4(X9,X10,X9),k4_xboole_0(X11,X9)) )
    | ~ spl5_8
    | ~ spl5_29 ),
    inference(resolution,[],[f243,f68])).

fof(f68,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f242])).

fof(f957,plain,
    ( spl5_59
    | ~ spl5_11
    | ~ spl5_24
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f287,f262,f176,f79,f955])).

fof(f79,plain,
    ( spl5_11
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f176,plain,
    ( spl5_24
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f287,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))
    | ~ spl5_11
    | ~ spl5_24
    | ~ spl5_31 ),
    inference(forward_demodulation,[],[f279,f80])).

fof(f80,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f279,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))
    | ~ spl5_24
    | ~ spl5_31 ),
    inference(superposition,[],[f177,f263])).

fof(f177,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f176])).

fof(f730,plain,
    ( spl5_52
    | ~ spl5_21
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f256,f242,f162,f728])).

fof(f162,plain,
    ( spl5_21
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK4(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(sK4(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f256,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2) )
    | ~ spl5_21
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f254,f243])).

fof(f254,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2)
        | ~ r2_hidden(sK4(X1,X2,X1),X1) )
    | ~ spl5_21
    | ~ spl5_29 ),
    inference(duplicate_literal_removal,[],[f246])).

fof(f246,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2)
        | ~ r2_hidden(sK4(X1,X2,X1),X1)
        | k4_xboole_0(X1,X2) = X1 )
    | ~ spl5_21
    | ~ spl5_29 ),
    inference(resolution,[],[f243,f163])).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(sK4(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f162])).

fof(f291,plain,
    ( spl5_32
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f101,f83,f75,f289])).

fof(f75,plain,
    ( spl5_10
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f83,plain,
    ( spl5_12
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f101,plain,
    ( ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(superposition,[],[f84,f76])).

fof(f76,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f84,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f264,plain,
    ( spl5_31
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f98,f79,f75,f51,f47,f262])).

fof(f47,plain,
    ( spl5_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f51,plain,
    ( spl5_4
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f98,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f97,f52])).

fof(f52,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f97,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f95,f48])).

fof(f48,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f95,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(superposition,[],[f76,f80])).

fof(f244,plain,
    ( spl5_29
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f153,f137,f242])).

fof(f137,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK4(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl5_18 ),
    inference(factoring,[],[f138])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(X0,X1,X2),X2)
        | r2_hidden(sK4(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f178,plain,
    ( spl5_24
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f99,f83,f47,f176])).

fof(f99,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(superposition,[],[f84,f48])).

fof(f164,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f29,f162])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f139,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f30,f137])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f85,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f23,f83])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f81,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f22,f79])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f77,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f21,f75])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f69,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f53,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f49,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f41,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (13506)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (13500)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (13500)Refutation not found, incomplete strategy% (13500)------------------------------
% 0.21/0.48  % (13500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13490)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (13491)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (13491)Refutation not found, incomplete strategy% (13491)------------------------------
% 0.21/0.48  % (13491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13491)Memory used [KB]: 10618
% 0.21/0.48  % (13491)Time elapsed: 0.062 s
% 0.21/0.48  % (13491)------------------------------
% 0.21/0.48  % (13491)------------------------------
% 0.21/0.49  % (13494)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (13499)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (13498)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (13495)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (13500)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13500)Memory used [KB]: 6012
% 0.21/0.49  % (13500)Time elapsed: 0.003 s
% 0.21/0.49  % (13500)------------------------------
% 0.21/0.49  % (13500)------------------------------
% 0.21/0.49  % (13498)Refutation not found, incomplete strategy% (13498)------------------------------
% 0.21/0.49  % (13498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13498)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13498)Memory used [KB]: 6012
% 0.21/0.49  % (13498)Time elapsed: 0.036 s
% 0.21/0.49  % (13498)------------------------------
% 0.21/0.49  % (13498)------------------------------
% 0.21/0.49  % (13499)Refutation not found, incomplete strategy% (13499)------------------------------
% 0.21/0.49  % (13499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13499)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13499)Memory used [KB]: 10618
% 0.21/0.49  % (13499)Time elapsed: 0.073 s
% 0.21/0.49  % (13499)------------------------------
% 0.21/0.49  % (13499)------------------------------
% 0.21/0.50  % (13503)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (13503)Refutation not found, incomplete strategy% (13503)------------------------------
% 0.21/0.50  % (13503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13503)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13503)Memory used [KB]: 6140
% 0.21/0.50  % (13503)Time elapsed: 0.047 s
% 0.21/0.50  % (13503)------------------------------
% 0.21/0.50  % (13503)------------------------------
% 0.21/0.50  % (13496)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (13508)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (13493)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (13492)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (13505)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (13504)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (13489)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (13488)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (13507)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (13489)Refutation not found, incomplete strategy% (13489)------------------------------
% 0.21/0.51  % (13489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13489)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13489)Memory used [KB]: 10490
% 0.21/0.51  % (13489)Time elapsed: 0.094 s
% 0.21/0.51  % (13489)------------------------------
% 0.21/0.51  % (13489)------------------------------
% 0.21/0.51  % (13488)Refutation not found, incomplete strategy% (13488)------------------------------
% 0.21/0.51  % (13488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13488)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13488)Memory used [KB]: 6140
% 0.21/0.51  % (13488)Time elapsed: 0.096 s
% 0.21/0.51  % (13488)------------------------------
% 0.21/0.51  % (13488)------------------------------
% 0.21/0.51  % (13508)Refutation not found, incomplete strategy% (13508)------------------------------
% 0.21/0.51  % (13508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13508)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13508)Memory used [KB]: 10490
% 0.21/0.51  % (13508)Time elapsed: 0.095 s
% 0.21/0.51  % (13508)------------------------------
% 0.21/0.51  % (13508)------------------------------
% 0.21/0.51  % (13502)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (13497)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (13501)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (13501)Refutation not found, incomplete strategy% (13501)------------------------------
% 0.21/0.52  % (13501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13501)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13501)Memory used [KB]: 1535
% 0.21/0.52  % (13501)Time elapsed: 0.108 s
% 0.21/0.52  % (13501)------------------------------
% 0.21/0.52  % (13501)------------------------------
% 0.21/0.55  % (13497)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1366,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f41,f49,f53,f69,f77,f81,f85,f139,f164,f178,f244,f264,f291,f730,f957,f1063,f1118,f1276,f1317])).
% 0.21/0.57  fof(f1317,plain,(
% 0.21/0.57    spl5_1 | ~spl5_67),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f1277])).
% 0.21/0.57  fof(f1277,plain,(
% 0.21/0.57    $false | (spl5_1 | ~spl5_67)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f40,f1275])).
% 0.21/0.57  fof(f1275,plain,(
% 0.21/0.57    ( ! [X24,X25] : (k3_xboole_0(X24,X25) = k4_xboole_0(X24,k4_xboole_0(X24,X25))) ) | ~spl5_67),
% 0.21/0.57    inference(avatar_component_clause,[],[f1274])).
% 0.21/0.57  fof(f1274,plain,(
% 0.21/0.57    spl5_67 <=> ! [X25,X24] : k3_xboole_0(X24,X25) = k4_xboole_0(X24,k4_xboole_0(X24,X25))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl5_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    spl5_1 <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.57  fof(f1276,plain,(
% 0.21/0.57    spl5_67 | ~spl5_31 | ~spl5_59 | ~spl5_65),
% 0.21/0.57    inference(avatar_split_clause,[],[f1173,f1116,f955,f262,f1274])).
% 0.21/0.57  fof(f262,plain,(
% 0.21/0.57    spl5_31 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.57  fof(f955,plain,(
% 0.21/0.57    spl5_59 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 0.21/0.57  fof(f1116,plain,(
% 0.21/0.57    spl5_65 <=> ! [X7,X6] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 0.21/0.57  fof(f1173,plain,(
% 0.21/0.57    ( ! [X24,X25] : (k3_xboole_0(X24,X25) = k4_xboole_0(X24,k4_xboole_0(X24,X25))) ) | (~spl5_31 | ~spl5_59 | ~spl5_65)),
% 0.21/0.57    inference(forward_demodulation,[],[f1132,f956])).
% 0.21/0.57  fof(f956,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) ) | ~spl5_59),
% 0.21/0.57    inference(avatar_component_clause,[],[f955])).
% 0.21/0.57  fof(f1132,plain,(
% 0.21/0.57    ( ! [X24,X25] : (k3_xboole_0(X24,X25) = k4_xboole_0(X24,k4_xboole_0(k4_xboole_0(X24,X25),k3_xboole_0(X24,X25)))) ) | (~spl5_31 | ~spl5_65)),
% 0.21/0.57    inference(superposition,[],[f1117,f263])).
% 0.21/0.57  fof(f263,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl5_31),
% 0.21/0.57    inference(avatar_component_clause,[],[f262])).
% 0.21/0.57  fof(f1117,plain,(
% 0.21/0.57    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6) ) | ~spl5_65),
% 0.21/0.57    inference(avatar_component_clause,[],[f1116])).
% 0.21/0.57  fof(f1118,plain,(
% 0.21/0.57    spl5_65 | ~spl5_32 | ~spl5_52 | ~spl5_62),
% 0.21/0.57    inference(avatar_split_clause,[],[f1084,f1061,f728,f289,f1116])).
% 0.21/0.57  fof(f289,plain,(
% 0.21/0.57    spl5_32 <=> ! [X7,X6] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.57  fof(f728,plain,(
% 0.21/0.57    spl5_52 <=> ! [X1,X2] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.21/0.57  fof(f1061,plain,(
% 0.21/0.57    spl5_62 <=> ! [X9,X11,X10] : (k4_xboole_0(X9,X10) = X9 | ~r2_hidden(sK4(X9,X10,X9),k4_xboole_0(X11,X9)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 0.21/0.57  fof(f1084,plain,(
% 0.21/0.57    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6) ) | (~spl5_32 | ~spl5_52 | ~spl5_62)),
% 0.21/0.57    inference(backward_demodulation,[],[f290,f1083])).
% 0.21/0.57  fof(f1083,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) ) | (~spl5_52 | ~spl5_62)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f1068])).
% 0.21/0.57  fof(f1068,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 | k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) ) | (~spl5_52 | ~spl5_62)),
% 0.21/0.57    inference(resolution,[],[f1062,f729])).
% 0.21/0.57  fof(f729,plain,(
% 0.21/0.57    ( ! [X2,X1] : (r2_hidden(sK4(X1,X2,X1),X2) | k4_xboole_0(X1,X2) = X1) ) | ~spl5_52),
% 0.21/0.57    inference(avatar_component_clause,[],[f728])).
% 0.21/0.57  fof(f1062,plain,(
% 0.21/0.57    ( ! [X10,X11,X9] : (~r2_hidden(sK4(X9,X10,X9),k4_xboole_0(X11,X9)) | k4_xboole_0(X9,X10) = X9) ) | ~spl5_62),
% 0.21/0.57    inference(avatar_component_clause,[],[f1061])).
% 0.21/0.57  fof(f290,plain,(
% 0.21/0.57    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))) ) | ~spl5_32),
% 0.21/0.57    inference(avatar_component_clause,[],[f289])).
% 0.21/0.57  fof(f1063,plain,(
% 0.21/0.57    spl5_62 | ~spl5_8 | ~spl5_29),
% 0.21/0.57    inference(avatar_split_clause,[],[f249,f242,f67,f1061])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    spl5_8 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.57  fof(f242,plain,(
% 0.21/0.57    spl5_29 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.57  fof(f249,plain,(
% 0.21/0.57    ( ! [X10,X11,X9] : (k4_xboole_0(X9,X10) = X9 | ~r2_hidden(sK4(X9,X10,X9),k4_xboole_0(X11,X9))) ) | (~spl5_8 | ~spl5_29)),
% 0.21/0.57    inference(resolution,[],[f243,f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) ) | ~spl5_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f67])).
% 0.21/0.57  fof(f243,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl5_29),
% 0.21/0.57    inference(avatar_component_clause,[],[f242])).
% 0.21/0.57  fof(f957,plain,(
% 0.21/0.57    spl5_59 | ~spl5_11 | ~spl5_24 | ~spl5_31),
% 0.21/0.57    inference(avatar_split_clause,[],[f287,f262,f176,f79,f955])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    spl5_11 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.57  fof(f176,plain,(
% 0.21/0.57    spl5_24 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.57  fof(f287,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) ) | (~spl5_11 | ~spl5_24 | ~spl5_31)),
% 0.21/0.57    inference(forward_demodulation,[],[f279,f80])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl5_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f79])).
% 0.21/0.57  fof(f279,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) ) | (~spl5_24 | ~spl5_31)),
% 0.21/0.57    inference(superposition,[],[f177,f263])).
% 0.21/0.57  fof(f177,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | ~spl5_24),
% 0.21/0.57    inference(avatar_component_clause,[],[f176])).
% 0.21/0.57  fof(f730,plain,(
% 0.21/0.57    spl5_52 | ~spl5_21 | ~spl5_29),
% 0.21/0.57    inference(avatar_split_clause,[],[f256,f242,f162,f728])).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    spl5_21 <=> ! [X1,X0,X2] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.57  fof(f256,plain,(
% 0.21/0.57    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2)) ) | (~spl5_21 | ~spl5_29)),
% 0.21/0.57    inference(subsumption_resolution,[],[f254,f243])).
% 0.21/0.57  fof(f254,plain,(
% 0.21/0.57    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2) | ~r2_hidden(sK4(X1,X2,X1),X1)) ) | (~spl5_21 | ~spl5_29)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f246])).
% 0.21/0.57  fof(f246,plain,(
% 0.21/0.57    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2) | ~r2_hidden(sK4(X1,X2,X1),X1) | k4_xboole_0(X1,X2) = X1) ) | (~spl5_21 | ~spl5_29)),
% 0.21/0.57    inference(resolution,[],[f243,f163])).
% 0.21/0.57  fof(f163,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl5_21),
% 0.21/0.57    inference(avatar_component_clause,[],[f162])).
% 0.21/0.57  fof(f291,plain,(
% 0.21/0.57    spl5_32 | ~spl5_10 | ~spl5_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f101,f83,f75,f289])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    spl5_10 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    spl5_12 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))) ) | (~spl5_10 | ~spl5_12)),
% 0.21/0.57    inference(superposition,[],[f84,f76])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl5_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f75])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl5_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f83])).
% 0.21/0.57  fof(f264,plain,(
% 0.21/0.57    spl5_31 | ~spl5_3 | ~spl5_4 | ~spl5_10 | ~spl5_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f98,f79,f75,f51,f47,f262])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    spl5_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    spl5_4 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | (~spl5_3 | ~spl5_4 | ~spl5_10 | ~spl5_11)),
% 0.21/0.57    inference(forward_demodulation,[],[f97,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl5_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f51])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl5_3 | ~spl5_10 | ~spl5_11)),
% 0.21/0.57    inference(forward_demodulation,[],[f95,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl5_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f47])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl5_10 | ~spl5_11)),
% 0.21/0.57    inference(superposition,[],[f76,f80])).
% 0.21/0.57  fof(f244,plain,(
% 0.21/0.57    spl5_29 | ~spl5_18),
% 0.21/0.57    inference(avatar_split_clause,[],[f153,f137,f242])).
% 0.21/0.57  fof(f137,plain,(
% 0.21/0.57    spl5_18 <=> ! [X1,X0,X2] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl5_18),
% 0.21/0.57    inference(factoring,[],[f138])).
% 0.21/0.57  fof(f138,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl5_18),
% 0.21/0.57    inference(avatar_component_clause,[],[f137])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    spl5_24 | ~spl5_3 | ~spl5_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f99,f83,f47,f176])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | (~spl5_3 | ~spl5_12)),
% 0.21/0.57    inference(superposition,[],[f84,f48])).
% 0.21/0.57  fof(f164,plain,(
% 0.21/0.57    spl5_21),
% 0.21/0.57    inference(avatar_split_clause,[],[f29,f162])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    spl5_18),
% 0.21/0.57    inference(avatar_split_clause,[],[f30,f137])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    spl5_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f23,f83])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    spl5_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f22,f79])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    spl5_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f21,f75])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    spl5_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f36,f67])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    spl5_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f20,f51])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    spl5_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f19,f47])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ~spl5_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.57    inference(negated_conjecture,[],[f10])).
% 0.21/0.57  fof(f10,conjecture,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (13497)------------------------------
% 0.21/0.57  % (13497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (13497)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (13497)Memory used [KB]: 11513
% 0.21/0.57  % (13497)Time elapsed: 0.132 s
% 0.21/0.57  % (13497)------------------------------
% 0.21/0.57  % (13497)------------------------------
% 0.21/0.57  % (13487)Success in time 0.204 s
%------------------------------------------------------------------------------
