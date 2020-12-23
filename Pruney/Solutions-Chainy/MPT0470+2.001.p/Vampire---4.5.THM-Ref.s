%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:43 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 355 expanded)
%              Number of leaves         :   42 ( 150 expanded)
%              Depth                    :   13
%              Number of atoms          :  444 ( 943 expanded)
%              Number of equality atoms :   65 ( 128 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1709,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f112,f115,f125,f141,f145,f151,f189,f196,f219,f228,f272,f275,f300,f305,f320,f351,f1099,f1187,f1190,f1209,f1669,f1708])).

fof(f1708,plain,
    ( k1_xboole_0 != k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | k4_relat_1(k1_xboole_0) != k5_relat_1(k4_relat_1(k1_xboole_0),sK0)
    | k1_xboole_0 != k4_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1669,plain,
    ( spl3_184
    | ~ spl3_22
    | ~ spl3_4
    | ~ spl3_34
    | ~ spl3_37
    | ~ spl3_136 ),
    inference(avatar_split_clause,[],[f1665,f1207,f349,f318,f75,f245,f1667])).

fof(f1667,plain,
    ( spl3_184
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_184])])).

fof(f245,plain,
    ( spl3_22
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f75,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f318,plain,
    ( spl3_34
  <=> k1_xboole_0 = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f349,plain,
    ( spl3_37
  <=> k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f1207,plain,
    ( spl3_136
  <=> k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_136])])).

fof(f1665,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_34
    | ~ spl3_37
    | ~ spl3_136 ),
    inference(forward_demodulation,[],[f1664,f350])).

fof(f350,plain,
    ( k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f349])).

fof(f1664,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | ~ spl3_4
    | ~ spl3_34
    | ~ spl3_37
    | ~ spl3_136 ),
    inference(forward_demodulation,[],[f1663,f1208])).

fof(f1208,plain,
    ( k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_136 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f1663,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | ~ spl3_4
    | ~ spl3_34
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f1653,f350])).

fof(f1653,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k5_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | ~ spl3_4
    | ~ spl3_34 ),
    inference(superposition,[],[f422,f319])).

fof(f319,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f318])).

fof(f422,plain,
    ( ! [X3] :
        ( k4_relat_1(k5_relat_1(X3,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X3))
        | ~ v1_relat_1(X3) )
    | ~ spl3_4 ),
    inference(resolution,[],[f176,f76])).

fof(f76,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(resolution,[],[f50,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f1209,plain,
    ( spl3_136
    | ~ spl3_133 ),
    inference(avatar_split_clause,[],[f1197,f1185,f1207])).

fof(f1185,plain,
    ( spl3_133
  <=> v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_133])])).

fof(f1197,plain,
    ( k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_133 ),
    inference(resolution,[],[f1186,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1186,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl3_133 ),
    inference(avatar_component_clause,[],[f1185])).

fof(f1190,plain,
    ( ~ spl3_22
    | ~ spl3_7
    | spl3_130 ),
    inference(avatar_split_clause,[],[f1188,f1174,f107,f245])).

fof(f107,plain,
    ( spl3_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1174,plain,
    ( spl3_130
  <=> v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_130])])).

fof(f1188,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl3_130 ),
    inference(resolution,[],[f1175,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f1175,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | spl3_130 ),
    inference(avatar_component_clause,[],[f1174])).

fof(f1187,plain,
    ( spl3_133
    | ~ spl3_130
    | ~ spl3_4
    | ~ spl3_120 ),
    inference(avatar_split_clause,[],[f1171,f1097,f75,f1174,f1185])).

fof(f1097,plain,
    ( spl3_120
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_120])])).

fof(f1171,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl3_120 ),
    inference(superposition,[],[f51,f1098])).

fof(f1098,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl3_120 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f1099,plain,
    ( spl3_120
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f1086,f245,f110,f75,f1097])).

fof(f110,plain,
    ( spl3_8
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f1086,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_22 ),
    inference(resolution,[],[f1043,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f111,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(resolution,[],[f96,f76])).

fof(f96,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(X4)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f93,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0),X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f92,f46])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(sK1(X0),X1) ) ),
    inference(resolution,[],[f58,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f111,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1043,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f245])).

fof(f351,plain,
    ( ~ spl3_25
    | spl3_37
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f332,f318,f349,f255])).

fof(f255,plain,
    ( spl3_25
  <=> v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f332,plain,
    ( k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | ~ spl3_34 ),
    inference(superposition,[],[f48,f319])).

fof(f48,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f320,plain,
    ( spl3_34
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f312,f270,f318])).

fof(f270,plain,
    ( spl3_29
  <=> v1_xboole_0(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f312,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | ~ spl3_29 ),
    inference(resolution,[],[f271,f46])).

fof(f271,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f270])).

fof(f305,plain,
    ( ~ spl3_22
    | ~ spl3_3
    | spl3_25 ),
    inference(avatar_split_clause,[],[f303,f255,f71,f245])).

fof(f71,plain,
    ( spl3_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f303,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl3_25 ),
    inference(resolution,[],[f256,f54])).

fof(f256,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f255])).

fof(f300,plain,
    ( ~ spl3_25
    | spl3_24 ),
    inference(avatar_split_clause,[],[f297,f252,f255])).

fof(f252,plain,
    ( spl3_24
  <=> v1_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f297,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | spl3_24 ),
    inference(resolution,[],[f253,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f253,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f252])).

fof(f275,plain,
    ( ~ spl3_7
    | spl3_22 ),
    inference(avatar_split_clause,[],[f273,f245,f107])).

fof(f273,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_22 ),
    inference(resolution,[],[f246,f47])).

fof(f246,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f245])).

fof(f272,plain,
    ( spl3_29
    | ~ spl3_24
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f239,f226,f75,f252,f270])).

fof(f226,plain,
    ( spl3_19
  <=> k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f239,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)))
    | ~ spl3_19 ),
    inference(superposition,[],[f51,f227])).

fof(f227,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f226])).

fof(f228,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f223,f217,f75,f226])).

fof(f217,plain,
    ( spl3_18
  <=> r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f223,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)))
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(resolution,[],[f218,f97])).

fof(f218,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))),k1_xboole_0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( ~ spl3_7
    | spl3_18
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f214,f187,f79,f217,f107])).

fof(f79,plain,
    ( spl3_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f187,plain,
    ( spl3_15
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X0,sK0))),k2_relat_1(k4_relat_1(X0)))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k4_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f214,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(superposition,[],[f211,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f211,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),sK0))),k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_15 ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),sK0))),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_15 ),
    inference(resolution,[],[f205,f47])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k4_relat_1(X0))
        | r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),sK0))),k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_15 ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),sK0))),k2_relat_1(X0))
        | ~ v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_15 ),
    inference(superposition,[],[f188,f48])).

fof(f188,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X0,sK0))),k2_relat_1(k4_relat_1(X0)))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k4_relat_1(X0)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f187])).

fof(f196,plain,
    ( ~ spl3_3
    | spl3_14 ),
    inference(avatar_split_clause,[],[f194,f184,f71])).

fof(f184,plain,
    ( spl3_14
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f194,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_14 ),
    inference(resolution,[],[f185,f47])).

fof(f185,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f189,plain,
    ( ~ spl3_14
    | spl3_15
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f181,f71,f187,f184])).

fof(f181,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X0,sK0))),k2_relat_1(k4_relat_1(X0)))
        | ~ v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f179])).

fof(f179,plain,
    ( ! [X7] :
        ( k4_relat_1(k5_relat_1(X7,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X7))
        | ~ v1_relat_1(X7) )
    | ~ spl3_3 ),
    inference(resolution,[],[f50,f72])).

fof(f72,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f151,plain,
    ( spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f149,f139,f67])).

fof(f67,plain,
    ( spl3_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f139,plain,
    ( spl3_12
  <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f149,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl3_12 ),
    inference(resolution,[],[f140,f46])).

fof(f140,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f145,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | spl3_10 ),
    inference(avatar_split_clause,[],[f142,f132,f107,f71])).

fof(f132,plain,
    ( spl3_10
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f142,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl3_10 ),
    inference(resolution,[],[f133,f54])).

fof(f133,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f141,plain,
    ( spl3_12
    | ~ spl3_10
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f129,f123,f75,f132,f139])).

fof(f123,plain,
    ( spl3_9
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f129,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_9 ),
    inference(superposition,[],[f51,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f121,f110,f75,f71,f123])).

fof(f121,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f116,f72])).

fof(f115,plain,
    ( ~ spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f113,f107,f75])).

fof(f113,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_7 ),
    inference(resolution,[],[f108,f45])).

fof(f108,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f112,plain,
    ( ~ spl3_7
    | spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f105,f79,f110,f107])).

fof(f105,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(superposition,[],[f49,f80])).

fof(f81,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f77,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f42,f75])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f73,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f69,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f41,f67,f64])).

fof(f64,plain,
    ( spl3_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (14600)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.49  % (14608)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (14603)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (14593)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (14597)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (14594)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (14609)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (14595)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (14614)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (14604)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (14606)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (14614)Refutation not found, incomplete strategy% (14614)------------------------------
% 0.20/0.52  % (14614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14614)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (14614)Memory used [KB]: 10618
% 0.20/0.52  % (14614)Time elapsed: 0.081 s
% 0.20/0.52  % (14614)------------------------------
% 0.20/0.52  % (14614)------------------------------
% 0.20/0.52  % (14613)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (14617)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (14598)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (14601)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (14592)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (14609)Refutation not found, incomplete strategy% (14609)------------------------------
% 0.20/0.53  % (14609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14609)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (14609)Memory used [KB]: 10618
% 0.20/0.53  % (14609)Time elapsed: 0.130 s
% 0.20/0.53  % (14609)------------------------------
% 0.20/0.53  % (14609)------------------------------
% 0.20/0.53  % (14605)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (14602)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (14621)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (14619)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (14611)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (14612)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (14607)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (14615)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (14599)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (14618)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (14610)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (14596)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.49/0.56  % (14616)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.56  % (14620)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.69/0.63  % (14611)Refutation found. Thanks to Tanya!
% 1.69/0.63  % SZS status Theorem for theBenchmark
% 1.69/0.63  % SZS output start Proof for theBenchmark
% 1.69/0.63  fof(f1709,plain,(
% 1.69/0.63    $false),
% 1.69/0.63    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f112,f115,f125,f141,f145,f151,f189,f196,f219,f228,f272,f275,f300,f305,f320,f351,f1099,f1187,f1190,f1209,f1669,f1708])).
% 1.69/0.63  fof(f1708,plain,(
% 1.69/0.63    k1_xboole_0 != k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | k4_relat_1(k1_xboole_0) != k5_relat_1(k4_relat_1(k1_xboole_0),sK0) | k1_xboole_0 != k4_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.69/0.63    introduced(theory_tautology_sat_conflict,[])).
% 1.69/0.63  fof(f1669,plain,(
% 1.69/0.63    spl3_184 | ~spl3_22 | ~spl3_4 | ~spl3_34 | ~spl3_37 | ~spl3_136),
% 1.69/0.63    inference(avatar_split_clause,[],[f1665,f1207,f349,f318,f75,f245,f1667])).
% 1.69/0.63  fof(f1667,plain,(
% 1.69/0.63    spl3_184 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_184])])).
% 1.69/0.63  fof(f245,plain,(
% 1.69/0.63    spl3_22 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.69/0.63  fof(f75,plain,(
% 1.69/0.63    spl3_4 <=> v1_xboole_0(k1_xboole_0)),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.69/0.63  fof(f318,plain,(
% 1.69/0.63    spl3_34 <=> k1_xboole_0 = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.69/0.63  fof(f349,plain,(
% 1.69/0.63    spl3_37 <=> k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0)),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.69/0.63  fof(f1207,plain,(
% 1.69/0.63    spl3_136 <=> k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_136])])).
% 1.69/0.63  fof(f1665,plain,(
% 1.69/0.63    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl3_4 | ~spl3_34 | ~spl3_37 | ~spl3_136)),
% 1.69/0.63    inference(forward_demodulation,[],[f1664,f350])).
% 1.69/0.63  fof(f350,plain,(
% 1.69/0.63    k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0) | ~spl3_37),
% 1.69/0.63    inference(avatar_component_clause,[],[f349])).
% 1.69/0.63  fof(f1664,plain,(
% 1.69/0.63    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | (~spl3_4 | ~spl3_34 | ~spl3_37 | ~spl3_136)),
% 1.69/0.63    inference(forward_demodulation,[],[f1663,f1208])).
% 1.69/0.63  fof(f1208,plain,(
% 1.69/0.63    k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) | ~spl3_136),
% 1.69/0.63    inference(avatar_component_clause,[],[f1207])).
% 1.69/0.63  fof(f1663,plain,(
% 1.69/0.63    k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | (~spl3_4 | ~spl3_34 | ~spl3_37)),
% 1.69/0.63    inference(forward_demodulation,[],[f1653,f350])).
% 1.69/0.63  fof(f1653,plain,(
% 1.69/0.63    k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k5_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | (~spl3_4 | ~spl3_34)),
% 1.69/0.63    inference(superposition,[],[f422,f319])).
% 1.69/0.63  fof(f319,plain,(
% 1.69/0.63    k1_xboole_0 = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | ~spl3_34),
% 1.69/0.63    inference(avatar_component_clause,[],[f318])).
% 1.69/0.63  fof(f422,plain,(
% 1.69/0.63    ( ! [X3] : (k4_relat_1(k5_relat_1(X3,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X3)) | ~v1_relat_1(X3)) ) | ~spl3_4),
% 1.69/0.63    inference(resolution,[],[f176,f76])).
% 1.69/0.63  fof(f76,plain,(
% 1.69/0.63    v1_xboole_0(k1_xboole_0) | ~spl3_4),
% 1.69/0.63    inference(avatar_component_clause,[],[f75])).
% 1.69/0.63  fof(f176,plain,(
% 1.69/0.63    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.69/0.63    inference(resolution,[],[f50,f45])).
% 1.69/0.63  fof(f45,plain,(
% 1.69/0.63    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.69/0.63    inference(cnf_transformation,[],[f17])).
% 1.69/0.63  fof(f17,plain,(
% 1.69/0.63    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.69/0.63    inference(ennf_transformation,[],[f6])).
% 1.69/0.63  fof(f6,axiom,(
% 1.69/0.63    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.69/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.69/0.63  fof(f50,plain,(
% 1.69/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.69/0.63    inference(cnf_transformation,[],[f22])).
% 1.69/0.63  fof(f22,plain,(
% 1.69/0.63    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.69/0.63    inference(ennf_transformation,[],[f12])).
% 1.69/0.63  fof(f12,axiom,(
% 1.69/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.69/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.69/0.63  fof(f1209,plain,(
% 1.69/0.63    spl3_136 | ~spl3_133),
% 1.69/0.63    inference(avatar_split_clause,[],[f1197,f1185,f1207])).
% 1.69/0.63  fof(f1185,plain,(
% 1.69/0.63    spl3_133 <=> v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_133])])).
% 1.69/0.63  fof(f1197,plain,(
% 1.69/0.63    k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) | ~spl3_133),
% 1.69/0.63    inference(resolution,[],[f1186,f46])).
% 1.69/0.63  fof(f46,plain,(
% 1.69/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.69/0.63    inference(cnf_transformation,[],[f18])).
% 1.69/0.63  fof(f18,plain,(
% 1.69/0.63    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.69/0.63    inference(ennf_transformation,[],[f4])).
% 1.69/0.63  fof(f4,axiom,(
% 1.69/0.63    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.69/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.69/0.63  fof(f1186,plain,(
% 1.69/0.63    v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~spl3_133),
% 1.69/0.63    inference(avatar_component_clause,[],[f1185])).
% 1.69/0.63  fof(f1190,plain,(
% 1.69/0.63    ~spl3_22 | ~spl3_7 | spl3_130),
% 1.69/0.63    inference(avatar_split_clause,[],[f1188,f1174,f107,f245])).
% 1.69/0.63  fof(f107,plain,(
% 1.69/0.63    spl3_7 <=> v1_relat_1(k1_xboole_0)),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.69/0.63  fof(f1174,plain,(
% 1.69/0.63    spl3_130 <=> v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_130])])).
% 1.69/0.63  fof(f1188,plain,(
% 1.69/0.63    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl3_130),
% 1.69/0.63    inference(resolution,[],[f1175,f54])).
% 1.69/0.63  fof(f54,plain,(
% 1.69/0.63    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.69/0.63    inference(cnf_transformation,[],[f26])).
% 1.69/0.63  fof(f26,plain,(
% 1.69/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.69/0.63    inference(flattening,[],[f25])).
% 1.69/0.63  fof(f25,plain,(
% 1.69/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.69/0.63    inference(ennf_transformation,[],[f8])).
% 1.69/0.63  fof(f8,axiom,(
% 1.69/0.63    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.69/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.69/0.63  fof(f1175,plain,(
% 1.69/0.63    ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | spl3_130),
% 1.69/0.63    inference(avatar_component_clause,[],[f1174])).
% 1.69/0.63  fof(f1187,plain,(
% 1.69/0.63    spl3_133 | ~spl3_130 | ~spl3_4 | ~spl3_120),
% 1.69/0.63    inference(avatar_split_clause,[],[f1171,f1097,f75,f1174,f1185])).
% 1.69/0.63  fof(f1097,plain,(
% 1.69/0.63    spl3_120 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_120])])).
% 1.69/0.63  fof(f1171,plain,(
% 1.69/0.63    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~spl3_120),
% 1.69/0.63    inference(superposition,[],[f51,f1098])).
% 1.69/0.63  fof(f1098,plain,(
% 1.69/0.63    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~spl3_120),
% 1.69/0.63    inference(avatar_component_clause,[],[f1097])).
% 1.69/0.63  fof(f51,plain,(
% 1.69/0.63    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.69/0.63    inference(cnf_transformation,[],[f24])).
% 1.69/0.63  fof(f24,plain,(
% 1.69/0.63    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.69/0.63    inference(flattening,[],[f23])).
% 1.69/0.63  fof(f23,plain,(
% 1.69/0.63    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.69/0.63    inference(ennf_transformation,[],[f9])).
% 1.69/0.63  fof(f9,axiom,(
% 1.69/0.63    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.69/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 1.69/0.63  fof(f1099,plain,(
% 1.69/0.63    spl3_120 | ~spl3_4 | ~spl3_8 | ~spl3_22),
% 1.69/0.63    inference(avatar_split_clause,[],[f1086,f245,f110,f75,f1097])).
% 1.69/0.63  fof(f110,plain,(
% 1.69/0.63    spl3_8 <=> ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 1.69/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.69/0.63  fof(f1086,plain,(
% 1.69/0.63    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl3_4 | ~spl3_8 | ~spl3_22)),
% 1.69/0.63    inference(resolution,[],[f1043,f116])).
% 1.69/0.63  fof(f116,plain,(
% 1.69/0.63    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | (~spl3_4 | ~spl3_8)),
% 1.69/0.63    inference(resolution,[],[f111,f97])).
% 1.69/0.63  fof(f97,plain,(
% 1.69/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_4),
% 1.69/0.63    inference(resolution,[],[f96,f76])).
% 1.69/0.63  fof(f96,plain,(
% 1.69/0.63    ( ! [X4,X3] : (~v1_xboole_0(X4) | k1_xboole_0 = X3 | ~r1_tarski(X3,X4)) )),
% 1.69/0.63    inference(resolution,[],[f93,f52])).
% 1.69/0.63  fof(f52,plain,(
% 1.69/0.63    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.69/0.63    inference(cnf_transformation,[],[f33])).
% 1.69/0.63  fof(f33,plain,(
% 1.69/0.63    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.69/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 1.69/0.63  fof(f32,plain,(
% 1.69/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.69/0.63    introduced(choice_axiom,[])).
% 1.69/0.63  fof(f31,plain,(
% 1.69/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.69/0.63    inference(rectify,[],[f30])).
% 1.69/0.63  fof(f30,plain,(
% 1.69/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.69/0.63    inference(nnf_transformation,[],[f1])).
% 1.69/0.63  fof(f1,axiom,(
% 1.69/0.63    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.69/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.69/0.63  fof(f93,plain,(
% 1.69/0.63    ( ! [X0,X1] : (r2_hidden(sK1(X0),X1) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0) )),
% 1.69/0.63    inference(resolution,[],[f92,f46])).
% 1.69/0.63  fof(f92,plain,(
% 1.69/0.63    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r1_tarski(X0,X1) | r2_hidden(sK1(X0),X1)) )),
% 1.69/0.63    inference(resolution,[],[f58,f53])).
% 1.69/0.63  fof(f53,plain,(
% 1.69/0.63    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 1.69/0.63    inference(cnf_transformation,[],[f33])).
% 1.69/0.63  fof(f58,plain,(
% 1.69/0.63    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.69/0.63    inference(cnf_transformation,[],[f39])).
% 1.69/0.63  fof(f39,plain,(
% 1.69/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 1.69/0.63  fof(f38,plain,(
% 1.69/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.69/0.63    introduced(choice_axiom,[])).
% 1.69/0.63  fof(f37,plain,(
% 1.69/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/0.63    inference(rectify,[],[f36])).
% 1.69/0.63  fof(f36,plain,(
% 1.69/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/0.63    inference(nnf_transformation,[],[f27])).
% 2.06/0.63  fof(f27,plain,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f2])).
% 2.06/0.63  fof(f2,axiom,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.06/0.63  fof(f111,plain,(
% 2.06/0.63    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_8),
% 2.06/0.63    inference(avatar_component_clause,[],[f110])).
% 2.06/0.63  fof(f1043,plain,(
% 2.06/0.63    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl3_22),
% 2.06/0.63    inference(avatar_component_clause,[],[f245])).
% 2.06/0.63  fof(f351,plain,(
% 2.06/0.63    ~spl3_25 | spl3_37 | ~spl3_34),
% 2.06/0.63    inference(avatar_split_clause,[],[f332,f318,f349,f255])).
% 2.06/0.63  fof(f255,plain,(
% 2.06/0.63    spl3_25 <=> v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.06/0.63  fof(f332,plain,(
% 2.06/0.63    k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),sK0) | ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | ~spl3_34),
% 2.06/0.63    inference(superposition,[],[f48,f319])).
% 2.06/0.63  fof(f48,plain,(
% 2.06/0.63    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f20])).
% 2.06/0.63  fof(f20,plain,(
% 2.06/0.63    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f10])).
% 2.06/0.63  fof(f10,axiom,(
% 2.06/0.63    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 2.06/0.63  fof(f320,plain,(
% 2.06/0.63    spl3_34 | ~spl3_29),
% 2.06/0.63    inference(avatar_split_clause,[],[f312,f270,f318])).
% 2.06/0.63  fof(f270,plain,(
% 2.06/0.63    spl3_29 <=> v1_xboole_0(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.06/0.63  fof(f312,plain,(
% 2.06/0.63    k1_xboole_0 = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | ~spl3_29),
% 2.06/0.63    inference(resolution,[],[f271,f46])).
% 2.06/0.63  fof(f271,plain,(
% 2.06/0.63    v1_xboole_0(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))) | ~spl3_29),
% 2.06/0.63    inference(avatar_component_clause,[],[f270])).
% 2.06/0.63  fof(f305,plain,(
% 2.06/0.63    ~spl3_22 | ~spl3_3 | spl3_25),
% 2.06/0.63    inference(avatar_split_clause,[],[f303,f255,f71,f245])).
% 2.06/0.63  fof(f71,plain,(
% 2.06/0.63    spl3_3 <=> v1_relat_1(sK0)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.06/0.63  fof(f303,plain,(
% 2.06/0.63    ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl3_25),
% 2.06/0.63    inference(resolution,[],[f256,f54])).
% 2.06/0.63  fof(f256,plain,(
% 2.06/0.63    ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | spl3_25),
% 2.06/0.63    inference(avatar_component_clause,[],[f255])).
% 2.06/0.63  fof(f300,plain,(
% 2.06/0.63    ~spl3_25 | spl3_24),
% 2.06/0.63    inference(avatar_split_clause,[],[f297,f252,f255])).
% 2.06/0.63  fof(f252,plain,(
% 2.06/0.63    spl3_24 <=> v1_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.06/0.63  fof(f297,plain,(
% 2.06/0.63    ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | spl3_24),
% 2.06/0.63    inference(resolution,[],[f253,f47])).
% 2.06/0.63  fof(f47,plain,(
% 2.06/0.63    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f19])).
% 2.06/0.63  fof(f19,plain,(
% 2.06/0.63    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f7])).
% 2.06/0.63  fof(f7,axiom,(
% 2.06/0.63    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.06/0.63  fof(f253,plain,(
% 2.06/0.63    ~v1_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))) | spl3_24),
% 2.06/0.63    inference(avatar_component_clause,[],[f252])).
% 2.06/0.63  fof(f275,plain,(
% 2.06/0.63    ~spl3_7 | spl3_22),
% 2.06/0.63    inference(avatar_split_clause,[],[f273,f245,f107])).
% 2.06/0.63  fof(f273,plain,(
% 2.06/0.63    ~v1_relat_1(k1_xboole_0) | spl3_22),
% 2.06/0.63    inference(resolution,[],[f246,f47])).
% 2.06/0.63  fof(f246,plain,(
% 2.06/0.63    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl3_22),
% 2.06/0.63    inference(avatar_component_clause,[],[f245])).
% 2.06/0.63  fof(f272,plain,(
% 2.06/0.63    spl3_29 | ~spl3_24 | ~spl3_4 | ~spl3_19),
% 2.06/0.63    inference(avatar_split_clause,[],[f239,f226,f75,f252,f270])).
% 2.06/0.63  fof(f226,plain,(
% 2.06/0.63    spl3_19 <=> k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.06/0.63  fof(f239,plain,(
% 2.06/0.63    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))) | v1_xboole_0(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))) | ~spl3_19),
% 2.06/0.63    inference(superposition,[],[f51,f227])).
% 2.06/0.63  fof(f227,plain,(
% 2.06/0.63    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))) | ~spl3_19),
% 2.06/0.63    inference(avatar_component_clause,[],[f226])).
% 2.06/0.63  fof(f228,plain,(
% 2.06/0.63    spl3_19 | ~spl3_4 | ~spl3_18),
% 2.06/0.63    inference(avatar_split_clause,[],[f223,f217,f75,f226])).
% 2.06/0.63  fof(f217,plain,(
% 2.06/0.63    spl3_18 <=> r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))),k1_xboole_0)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.06/0.63  fof(f223,plain,(
% 2.06/0.63    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))) | (~spl3_4 | ~spl3_18)),
% 2.06/0.63    inference(resolution,[],[f218,f97])).
% 2.06/0.63  fof(f218,plain,(
% 2.06/0.63    r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))),k1_xboole_0) | ~spl3_18),
% 2.06/0.63    inference(avatar_component_clause,[],[f217])).
% 2.06/0.63  fof(f219,plain,(
% 2.06/0.63    ~spl3_7 | spl3_18 | ~spl3_5 | ~spl3_15),
% 2.06/0.63    inference(avatar_split_clause,[],[f214,f187,f79,f217,f107])).
% 2.06/0.63  fof(f79,plain,(
% 2.06/0.63    spl3_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.06/0.63  fof(f187,plain,(
% 2.06/0.63    spl3_15 <=> ! [X0] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X0,sK0))),k2_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0) | ~v1_relat_1(k4_relat_1(X0)))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.06/0.63  fof(f214,plain,(
% 2.06/0.63    r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl3_5 | ~spl3_15)),
% 2.06/0.63    inference(superposition,[],[f211,f80])).
% 2.06/0.63  fof(f80,plain,(
% 2.06/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_5),
% 2.06/0.63    inference(avatar_component_clause,[],[f79])).
% 2.06/0.63  fof(f211,plain,(
% 2.06/0.63    ( ! [X0] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),sK0))),k2_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl3_15),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f206])).
% 2.06/0.63  fof(f206,plain,(
% 2.06/0.63    ( ! [X0] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),sK0))),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_15),
% 2.06/0.63    inference(resolution,[],[f205,f47])).
% 2.06/0.63  fof(f205,plain,(
% 2.06/0.63    ( ! [X0] : (~v1_relat_1(k4_relat_1(X0)) | r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),sK0))),k2_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl3_15),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f204])).
% 2.06/0.63  fof(f204,plain,(
% 2.06/0.63    ( ! [X0] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),sK0))),k2_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_15),
% 2.06/0.63    inference(superposition,[],[f188,f48])).
% 2.06/0.63  fof(f188,plain,(
% 2.06/0.63    ( ! [X0] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X0,sK0))),k2_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0) | ~v1_relat_1(k4_relat_1(X0))) ) | ~spl3_15),
% 2.06/0.63    inference(avatar_component_clause,[],[f187])).
% 2.06/0.63  fof(f196,plain,(
% 2.06/0.63    ~spl3_3 | spl3_14),
% 2.06/0.63    inference(avatar_split_clause,[],[f194,f184,f71])).
% 2.06/0.63  fof(f184,plain,(
% 2.06/0.63    spl3_14 <=> v1_relat_1(k4_relat_1(sK0))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.06/0.63  fof(f194,plain,(
% 2.06/0.63    ~v1_relat_1(sK0) | spl3_14),
% 2.06/0.63    inference(resolution,[],[f185,f47])).
% 2.06/0.63  fof(f185,plain,(
% 2.06/0.63    ~v1_relat_1(k4_relat_1(sK0)) | spl3_14),
% 2.06/0.63    inference(avatar_component_clause,[],[f184])).
% 2.06/0.63  fof(f189,plain,(
% 2.06/0.63    ~spl3_14 | spl3_15 | ~spl3_3),
% 2.06/0.63    inference(avatar_split_clause,[],[f181,f71,f187,f184])).
% 2.06/0.63  fof(f181,plain,(
% 2.06/0.63    ( ! [X0] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X0,sK0))),k2_relat_1(k4_relat_1(X0))) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(X0)) ) | ~spl3_3),
% 2.06/0.63    inference(superposition,[],[f49,f179])).
% 2.06/0.63  fof(f179,plain,(
% 2.06/0.63    ( ! [X7] : (k4_relat_1(k5_relat_1(X7,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X7)) | ~v1_relat_1(X7)) ) | ~spl3_3),
% 2.06/0.63    inference(resolution,[],[f50,f72])).
% 2.06/0.63  fof(f72,plain,(
% 2.06/0.63    v1_relat_1(sK0) | ~spl3_3),
% 2.06/0.63    inference(avatar_component_clause,[],[f71])).
% 2.06/0.63  fof(f49,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f21])).
% 2.06/0.63  fof(f21,plain,(
% 2.06/0.63    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f11])).
% 2.06/0.63  fof(f11,axiom,(
% 2.06/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 2.06/0.63  fof(f151,plain,(
% 2.06/0.63    spl3_2 | ~spl3_12),
% 2.06/0.63    inference(avatar_split_clause,[],[f149,f139,f67])).
% 2.06/0.63  fof(f67,plain,(
% 2.06/0.63    spl3_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.06/0.63  fof(f139,plain,(
% 2.06/0.63    spl3_12 <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.06/0.63  fof(f149,plain,(
% 2.06/0.63    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl3_12),
% 2.06/0.63    inference(resolution,[],[f140,f46])).
% 2.06/0.63  fof(f140,plain,(
% 2.06/0.63    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_12),
% 2.06/0.63    inference(avatar_component_clause,[],[f139])).
% 2.06/0.63  fof(f145,plain,(
% 2.06/0.63    ~spl3_3 | ~spl3_7 | spl3_10),
% 2.06/0.63    inference(avatar_split_clause,[],[f142,f132,f107,f71])).
% 2.06/0.63  fof(f132,plain,(
% 2.06/0.63    spl3_10 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.06/0.63  fof(f142,plain,(
% 2.06/0.63    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl3_10),
% 2.06/0.63    inference(resolution,[],[f133,f54])).
% 2.06/0.63  fof(f133,plain,(
% 2.06/0.63    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl3_10),
% 2.06/0.63    inference(avatar_component_clause,[],[f132])).
% 2.06/0.63  fof(f141,plain,(
% 2.06/0.63    spl3_12 | ~spl3_10 | ~spl3_4 | ~spl3_9),
% 2.06/0.63    inference(avatar_split_clause,[],[f129,f123,f75,f132,f139])).
% 2.06/0.63  fof(f123,plain,(
% 2.06/0.63    spl3_9 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.06/0.63  fof(f129,plain,(
% 2.06/0.63    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_9),
% 2.06/0.63    inference(superposition,[],[f51,f124])).
% 2.06/0.63  fof(f124,plain,(
% 2.06/0.63    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_9),
% 2.06/0.63    inference(avatar_component_clause,[],[f123])).
% 2.06/0.63  fof(f125,plain,(
% 2.06/0.63    spl3_9 | ~spl3_3 | ~spl3_4 | ~spl3_8),
% 2.06/0.63    inference(avatar_split_clause,[],[f121,f110,f75,f71,f123])).
% 2.06/0.63  fof(f121,plain,(
% 2.06/0.63    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl3_3 | ~spl3_4 | ~spl3_8)),
% 2.06/0.63    inference(resolution,[],[f116,f72])).
% 2.06/0.63  fof(f115,plain,(
% 2.06/0.63    ~spl3_4 | spl3_7),
% 2.06/0.63    inference(avatar_split_clause,[],[f113,f107,f75])).
% 2.06/0.63  fof(f113,plain,(
% 2.06/0.63    ~v1_xboole_0(k1_xboole_0) | spl3_7),
% 2.06/0.63    inference(resolution,[],[f108,f45])).
% 2.06/0.63  fof(f108,plain,(
% 2.06/0.63    ~v1_relat_1(k1_xboole_0) | spl3_7),
% 2.06/0.63    inference(avatar_component_clause,[],[f107])).
% 2.06/0.63  fof(f112,plain,(
% 2.06/0.63    ~spl3_7 | spl3_8 | ~spl3_5),
% 2.06/0.63    inference(avatar_split_clause,[],[f105,f79,f110,f107])).
% 2.06/0.63  fof(f105,plain,(
% 2.06/0.63    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_5),
% 2.06/0.63    inference(superposition,[],[f49,f80])).
% 2.06/0.63  fof(f81,plain,(
% 2.06/0.63    spl3_5),
% 2.06/0.63    inference(avatar_split_clause,[],[f44,f79])).
% 2.06/0.63  fof(f44,plain,(
% 2.06/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.06/0.63    inference(cnf_transformation,[],[f13])).
% 2.06/0.63  fof(f13,axiom,(
% 2.06/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.06/0.63  fof(f77,plain,(
% 2.06/0.63    spl3_4),
% 2.06/0.63    inference(avatar_split_clause,[],[f42,f75])).
% 2.06/0.63  fof(f42,plain,(
% 2.06/0.63    v1_xboole_0(k1_xboole_0)),
% 2.06/0.63    inference(cnf_transformation,[],[f3])).
% 2.06/0.63  fof(f3,axiom,(
% 2.06/0.63    v1_xboole_0(k1_xboole_0)),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.06/0.63  fof(f73,plain,(
% 2.06/0.63    spl3_3),
% 2.06/0.63    inference(avatar_split_clause,[],[f40,f71])).
% 2.06/0.63  fof(f40,plain,(
% 2.06/0.63    v1_relat_1(sK0)),
% 2.06/0.63    inference(cnf_transformation,[],[f29])).
% 2.06/0.63  fof(f29,plain,(
% 2.06/0.63    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).
% 2.06/0.63  fof(f28,plain,(
% 2.06/0.63    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f16,plain,(
% 2.06/0.63    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f15])).
% 2.06/0.63  fof(f15,negated_conjecture,(
% 2.06/0.63    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.06/0.63    inference(negated_conjecture,[],[f14])).
% 2.06/0.63  fof(f14,conjecture,(
% 2.06/0.63    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 2.06/0.63  fof(f69,plain,(
% 2.06/0.63    ~spl3_1 | ~spl3_2),
% 2.06/0.63    inference(avatar_split_clause,[],[f41,f67,f64])).
% 2.06/0.63  fof(f64,plain,(
% 2.06/0.63    spl3_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.06/0.63  fof(f41,plain,(
% 2.06/0.63    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 2.06/0.63    inference(cnf_transformation,[],[f29])).
% 2.06/0.63  % SZS output end Proof for theBenchmark
% 2.06/0.63  % (14611)------------------------------
% 2.06/0.63  % (14611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (14611)Termination reason: Refutation
% 2.06/0.63  
% 2.06/0.63  % (14611)Memory used [KB]: 12153
% 2.06/0.63  % (14611)Time elapsed: 0.226 s
% 2.06/0.63  % (14611)------------------------------
% 2.06/0.63  % (14611)------------------------------
% 2.06/0.64  % (14591)Success in time 0.278 s
%------------------------------------------------------------------------------
