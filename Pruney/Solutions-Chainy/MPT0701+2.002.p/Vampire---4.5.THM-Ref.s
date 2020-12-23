%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:10 EST 2020

% Result     : Theorem 3.03s
% Output     : Refutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 419 expanded)
%              Number of leaves         :   44 ( 193 expanded)
%              Depth                    :    8
%              Number of atoms          :  656 (1610 expanded)
%              Number of equality atoms :  116 ( 402 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3704,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f100,f105,f110,f119,f123,f141,f145,f160,f165,f287,f533,f537,f1315,f1348,f1357,f1362,f1395,f1404,f1417,f1422,f1519,f1528,f1633,f2798,f2808,f2883,f3003,f3107,f3132,f3698])).

fof(f3698,plain,
    ( spl9_291
    | ~ spl9_6
    | ~ spl9_154
    | ~ spl9_167
    | ~ spl9_180
    | ~ spl9_191
    | ~ spl9_366 ),
    inference(avatar_split_clause,[],[f3697,f3129,f1617,f1525,f1414,f1313,f82,f2594])).

fof(f2594,plain,
    ( spl9_291
  <=> sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_291])])).

fof(f82,plain,
    ( spl9_6
  <=> k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1313,plain,
    ( spl9_154
  <=> ! [X0] :
        ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).

fof(f1414,plain,
    ( spl9_167
  <=> sK5(sK3,sK2) = k1_funct_1(sK3,sK4(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_167])])).

fof(f1525,plain,
    ( spl9_180
  <=> sK4(sK3,sK2) = k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_180])])).

fof(f1617,plain,
    ( spl9_191
  <=> r2_hidden(sK7(sK1,sK4(sK3,sK2)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_191])])).

fof(f3129,plain,
    ( spl9_366
  <=> k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_366])])).

fof(f3697,plain,
    ( sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ spl9_6
    | ~ spl9_154
    | ~ spl9_167
    | ~ spl9_180
    | ~ spl9_191
    | ~ spl9_366 ),
    inference(forward_demodulation,[],[f3696,f1416])).

fof(f1416,plain,
    ( sK5(sK3,sK2) = k1_funct_1(sK3,sK4(sK3,sK2))
    | ~ spl9_167 ),
    inference(avatar_component_clause,[],[f1414])).

fof(f3696,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ spl9_6
    | ~ spl9_154
    | ~ spl9_180
    | ~ spl9_191
    | ~ spl9_366 ),
    inference(forward_demodulation,[],[f3695,f1527])).

fof(f1527,plain,
    ( sK4(sK3,sK2) = k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))
    | ~ spl9_180 ),
    inference(avatar_component_clause,[],[f1525])).

fof(f3695,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2))))
    | ~ spl9_6
    | ~ spl9_154
    | ~ spl9_191
    | ~ spl9_366 ),
    inference(forward_demodulation,[],[f3673,f3131])).

fof(f3131,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2)))
    | ~ spl9_366 ),
    inference(avatar_component_clause,[],[f3129])).

fof(f3673,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2)))
    | ~ spl9_6
    | ~ spl9_154
    | ~ spl9_191 ),
    inference(resolution,[],[f1316,f1618])).

fof(f1618,plain,
    ( r2_hidden(sK7(sK1,sK4(sK3,sK2)),k1_relat_1(sK1))
    | ~ spl9_191 ),
    inference(avatar_component_clause,[],[f1617])).

fof(f1316,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) )
    | ~ spl9_6
    | ~ spl9_154 ),
    inference(forward_demodulation,[],[f1314,f84])).

fof(f84,plain,
    ( k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f1314,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl9_154 ),
    inference(avatar_component_clause,[],[f1313])).

fof(f3132,plain,
    ( spl9_366
    | ~ spl9_158
    | ~ spl9_180
    | ~ spl9_191 ),
    inference(avatar_split_clause,[],[f3082,f1617,f1525,f1346,f3129])).

fof(f1346,plain,
    ( spl9_158
  <=> ! [X0] :
        ( k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).

fof(f3082,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2)))
    | ~ spl9_158
    | ~ spl9_180
    | ~ spl9_191 ),
    inference(forward_demodulation,[],[f3052,f1527])).

fof(f3052,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) = k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2))))
    | ~ spl9_158
    | ~ spl9_191 ),
    inference(resolution,[],[f1347,f1618])).

fof(f1347,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) )
    | ~ spl9_158 ),
    inference(avatar_component_clause,[],[f1346])).

fof(f3107,plain,
    ( ~ spl9_11
    | ~ spl9_10
    | spl9_272
    | ~ spl9_7
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f3106,f2806,f87,f2440,f102,f107])).

fof(f107,plain,
    ( spl9_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f102,plain,
    ( spl9_10
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f2440,plain,
    ( spl9_272
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK3,X1) = k1_funct_1(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_272])])).

fof(f87,plain,
    ( spl9_7
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f2806,plain,
    ( spl9_320
  <=> ! [X3,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | k1_funct_1(sK2,X2) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_320])])).

fof(f3106,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK3,X1) = k1_funct_1(sK2,X1)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl9_7
    | ~ spl9_320 ),
    inference(forward_demodulation,[],[f3100,f89])).

fof(f89,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f3100,plain,
    ( ! [X1] :
        ( k1_funct_1(sK3,X1) = k1_funct_1(sK2,X1)
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X1,k1_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl9_320 ),
    inference(resolution,[],[f2807,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f2807,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | k1_funct_1(sK2,X2) = X3 )
    | ~ spl9_320 ),
    inference(avatar_component_clause,[],[f2806])).

fof(f3003,plain,
    ( ~ spl9_11
    | ~ spl9_10
    | spl9_160
    | ~ spl9_162
    | ~ spl9_7
    | ~ spl9_331 ),
    inference(avatar_split_clause,[],[f3002,f2880,f87,f1371,f1359,f102,f107])).

fof(f1359,plain,
    ( spl9_160
  <=> r2_hidden(k4_tarski(sK4(sK2,sK3),sK5(sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).

fof(f1371,plain,
    ( spl9_162
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).

fof(f2880,plain,
    ( spl9_331
  <=> sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_331])])).

fof(f3002,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK4(sK2,sK3),sK5(sK2,sK3)),sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_7
    | ~ spl9_331 ),
    inference(forward_demodulation,[],[f2995,f89])).

fof(f2995,plain,
    ( r2_hidden(k4_tarski(sK4(sK2,sK3),sK5(sK2,sK3)),sK3)
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK4(sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl9_331 ),
    inference(superposition,[],[f55,f2882])).

fof(f2882,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl9_331 ),
    inference(avatar_component_clause,[],[f2880])).

fof(f2883,plain,
    ( spl9_331
    | ~ spl9_159
    | ~ spl9_162
    | ~ spl9_272 ),
    inference(avatar_split_clause,[],[f2878,f2440,f1371,f1354,f2880])).

fof(f1354,plain,
    ( spl9_159
  <=> k1_funct_1(sK2,sK4(sK2,sK3)) = sK5(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_159])])).

fof(f2878,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl9_159
    | ~ spl9_162
    | ~ spl9_272 ),
    inference(forward_demodulation,[],[f2823,f1356])).

fof(f1356,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = sK5(sK2,sK3)
    | ~ spl9_159 ),
    inference(avatar_component_clause,[],[f1354])).

fof(f2823,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl9_162
    | ~ spl9_272 ),
    inference(resolution,[],[f1372,f2441])).

fof(f2441,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK3,X1) = k1_funct_1(sK2,X1) )
    | ~ spl9_272 ),
    inference(avatar_component_clause,[],[f2440])).

fof(f1372,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl9_162 ),
    inference(avatar_component_clause,[],[f1371])).

fof(f2808,plain,
    ( ~ spl9_165
    | spl9_320
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f2530,f139,f107,f2806,f1400])).

fof(f1400,plain,
    ( spl9_165
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_165])])).

fof(f139,plain,
    ( spl9_16
  <=> ! [X3,X2] :
        ( k1_funct_1(sK2,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f2530,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | k1_funct_1(sK2,X2) = X3
        | ~ r1_tarski(sK3,sK2) )
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(resolution,[],[f562,f109])).

fof(f109,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f562,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X4)
        | ~ r2_hidden(k4_tarski(X2,X3),X4)
        | k1_funct_1(sK2,X2) = X3
        | ~ r1_tarski(X4,sK2) )
    | ~ spl9_16 ),
    inference(resolution,[],[f140,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f140,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | k1_funct_1(sK2,X2) = X3 )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f2798,plain,
    ( ~ spl9_4
    | ~ spl9_3
    | spl9_168
    | ~ spl9_177
    | ~ spl9_8
    | ~ spl9_291 ),
    inference(avatar_split_clause,[],[f2797,f2594,f92,f1486,f1419,f67,f72])).

fof(f72,plain,
    ( spl9_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f67,plain,
    ( spl9_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f1419,plain,
    ( spl9_168
  <=> r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_168])])).

fof(f1486,plain,
    ( spl9_177
  <=> r2_hidden(sK4(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_177])])).

fof(f92,plain,
    ( spl9_8
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f2797,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_8
    | ~ spl9_291 ),
    inference(forward_demodulation,[],[f2790,f94])).

fof(f94,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f2790,plain,
    ( r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK4(sK3,sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl9_291 ),
    inference(superposition,[],[f55,f2596])).

fof(f2596,plain,
    ( sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ spl9_291 ),
    inference(avatar_component_clause,[],[f2594])).

fof(f1633,plain,
    ( ~ spl9_2
    | ~ spl9_1
    | ~ spl9_177
    | ~ spl9_9
    | spl9_191 ),
    inference(avatar_split_clause,[],[f1632,f1617,f97,f1486,f57,f62])).

fof(f62,plain,
    ( spl9_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f57,plain,
    ( spl9_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f97,plain,
    ( spl9_9
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f1632,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_9
    | spl9_191 ),
    inference(forward_demodulation,[],[f1630,f99])).

fof(f99,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f1630,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK4(sK3,sK2),k2_relat_1(sK1))
    | spl9_191 ),
    inference(resolution,[],[f1619,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK7(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK7(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f1619,plain,
    ( ~ r2_hidden(sK7(sK1,sK4(sK3,sK2)),k1_relat_1(sK1))
    | spl9_191 ),
    inference(avatar_component_clause,[],[f1617])).

fof(f1528,plain,
    ( spl9_180
    | ~ spl9_37
    | ~ spl9_177 ),
    inference(avatar_split_clause,[],[f1522,f1486,f285,f1525])).

fof(f285,plain,
    ( spl9_37
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,sK7(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f1522,plain,
    ( sK4(sK3,sK2) = k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))
    | ~ spl9_37
    | ~ spl9_177 ),
    inference(resolution,[],[f1487,f286])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,sK7(sK1,X0)) = X0 )
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f285])).

fof(f1487,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ spl9_177 ),
    inference(avatar_component_clause,[],[f1486])).

fof(f1519,plain,
    ( spl9_165
    | ~ spl9_11
    | ~ spl9_12
    | spl9_177 ),
    inference(avatar_split_clause,[],[f1515,f1486,f117,f107,f1400])).

fof(f117,plain,
    ( spl9_12
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f1515,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(sK3,sK2)
    | ~ spl9_12
    | spl9_177 ),
    inference(resolution,[],[f1504,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1504,plain,
    ( ! [X2] : ~ r2_hidden(k4_tarski(sK4(sK3,sK2),X2),sK3)
    | ~ spl9_12
    | spl9_177 ),
    inference(resolution,[],[f1488,f118])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) )
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f1488,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | spl9_177 ),
    inference(avatar_component_clause,[],[f1486])).

fof(f1422,plain,
    ( ~ spl9_11
    | ~ spl9_168
    | spl9_165 ),
    inference(avatar_split_clause,[],[f1407,f1400,f1419,f107])).

fof(f1407,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | ~ v1_relat_1(sK3)
    | spl9_165 ),
    inference(resolution,[],[f1402,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1402,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl9_165 ),
    inference(avatar_component_clause,[],[f1400])).

fof(f1417,plain,
    ( spl9_167
    | ~ spl9_21
    | spl9_165 ),
    inference(avatar_split_clause,[],[f1406,f1400,f163,f1414])).

fof(f163,plain,
    ( spl9_21
  <=> ! [X0] :
        ( k1_funct_1(sK3,sK4(sK3,X0)) = sK5(sK3,X0)
        | r1_tarski(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f1406,plain,
    ( sK5(sK3,sK2) = k1_funct_1(sK3,sK4(sK3,sK2))
    | ~ spl9_21
    | spl9_165 ),
    inference(resolution,[],[f1402,f164])).

fof(f164,plain,
    ( ! [X0] :
        ( r1_tarski(sK3,X0)
        | k1_funct_1(sK3,sK4(sK3,X0)) = sK5(sK3,X0) )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f163])).

fof(f1404,plain,
    ( spl9_5
    | ~ spl9_165
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f1398,f1335,f1400,f77])).

fof(f77,plain,
    ( spl9_5
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f1335,plain,
    ( spl9_156
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_156])])).

fof(f1398,plain,
    ( ~ r1_tarski(sK3,sK2)
    | sK2 = sK3
    | ~ spl9_156 ),
    inference(resolution,[],[f1336,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1336,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl9_156 ),
    inference(avatar_component_clause,[],[f1335])).

fof(f1395,plain,
    ( spl9_156
    | ~ spl9_4
    | ~ spl9_13
    | spl9_162 ),
    inference(avatar_split_clause,[],[f1391,f1371,f121,f72,f1335])).

fof(f121,plain,
    ( spl9_13
  <=> ! [X3,X2] :
        ( r2_hidden(X2,sK0)
        | ~ r2_hidden(k4_tarski(X2,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f1391,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(sK2,sK3)
    | ~ spl9_13
    | spl9_162 ),
    inference(resolution,[],[f1387,f32])).

fof(f1387,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4(sK2,sK3),X0),sK2)
    | ~ spl9_13
    | spl9_162 ),
    inference(resolution,[],[f1373,f122])).

fof(f122,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK0)
        | ~ r2_hidden(k4_tarski(X2,X3),sK2) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f1373,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK0)
    | spl9_162 ),
    inference(avatar_component_clause,[],[f1371])).

fof(f1362,plain,
    ( ~ spl9_4
    | ~ spl9_160
    | spl9_156 ),
    inference(avatar_split_clause,[],[f1352,f1335,f1359,f72])).

fof(f1352,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK2,sK3),sK5(sK2,sK3)),sK3)
    | ~ v1_relat_1(sK2)
    | spl9_156 ),
    inference(resolution,[],[f1337,f33])).

fof(f1337,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl9_156 ),
    inference(avatar_component_clause,[],[f1335])).

fof(f1357,plain,
    ( spl9_159
    | ~ spl9_20
    | spl9_156 ),
    inference(avatar_split_clause,[],[f1351,f1335,f158,f1354])).

fof(f158,plain,
    ( spl9_20
  <=> ! [X0] :
        ( k1_funct_1(sK2,sK4(sK2,X0)) = sK5(sK2,X0)
        | r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f1351,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = sK5(sK2,sK3)
    | ~ spl9_20
    | spl9_156 ),
    inference(resolution,[],[f1337,f159])).

fof(f159,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,X0)
        | k1_funct_1(sK2,sK4(sK2,X0)) = sK5(sK2,X0) )
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1348,plain,
    ( ~ spl9_2
    | spl9_158
    | ~ spl9_1
    | ~ spl9_65 ),
    inference(avatar_split_clause,[],[f1342,f535,f57,f1346,f62])).

fof(f535,plain,
    ( spl9_65
  <=> ! [X5,X4] :
        ( ~ v1_funct_1(X4)
        | k1_funct_1(k5_relat_1(X4,sK2),X5) = k1_funct_1(sK2,k1_funct_1(X4,X5))
        | ~ r2_hidden(X5,k1_relat_1(X4))
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f1342,plain,
    ( ! [X0] :
        ( k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl9_1
    | ~ spl9_65 ),
    inference(resolution,[],[f536,f59])).

fof(f59,plain,
    ( v1_funct_1(sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f536,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_1(X4)
        | k1_funct_1(k5_relat_1(X4,sK2),X5) = k1_funct_1(sK2,k1_funct_1(X4,X5))
        | ~ r2_hidden(X5,k1_relat_1(X4))
        | ~ v1_relat_1(X4) )
    | ~ spl9_65 ),
    inference(avatar_component_clause,[],[f535])).

fof(f1315,plain,
    ( ~ spl9_2
    | spl9_154
    | ~ spl9_1
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f1302,f531,f57,f1313,f62])).

fof(f531,plain,
    ( spl9_64
  <=> ! [X3,X2] :
        ( ~ v1_funct_1(X2)
        | k1_funct_1(k5_relat_1(X2,sK3),X3) = k1_funct_1(sK3,k1_funct_1(X2,X3))
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f1302,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl9_1
    | ~ spl9_64 ),
    inference(resolution,[],[f532,f59])).

fof(f532,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | k1_funct_1(k5_relat_1(X2,sK3),X3) = k1_funct_1(sK3,k1_funct_1(X2,X3))
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | ~ v1_relat_1(X2) )
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f531])).

fof(f537,plain,
    ( ~ spl9_4
    | spl9_65
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f520,f67,f535,f72])).

fof(f520,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_1(X4)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X4)
        | ~ r2_hidden(X5,k1_relat_1(X4))
        | k1_funct_1(k5_relat_1(X4,sK2),X5) = k1_funct_1(sK2,k1_funct_1(X4,X5)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f40,f69])).

fof(f69,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f533,plain,
    ( ~ spl9_11
    | spl9_64
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f519,f102,f531,f107])).

fof(f519,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | k1_funct_1(k5_relat_1(X2,sK3),X3) = k1_funct_1(sK3,k1_funct_1(X2,X3)) )
    | ~ spl9_10 ),
    inference(resolution,[],[f40,f104])).

fof(f104,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f287,plain,
    ( ~ spl9_2
    | spl9_37
    | ~ spl9_1
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f283,f97,f57,f285,f62])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK1,sK7(sK1,X0)) = X0 )
    | ~ spl9_1
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f281,f99])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | k1_funct_1(sK1,sK7(sK1,X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f51,f59])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK7(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK7(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f165,plain,
    ( ~ spl9_11
    | spl9_21
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f161,f143,f163,f107])).

fof(f143,plain,
    ( spl9_17
  <=> ! [X5,X4] :
        ( k1_funct_1(sK3,X4) = X5
        | ~ r2_hidden(k4_tarski(X4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f161,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,sK4(sK3,X0)) = sK5(sK3,X0)
        | ~ v1_relat_1(sK3)
        | r1_tarski(sK3,X0) )
    | ~ spl9_17 ),
    inference(resolution,[],[f144,f32])).

fof(f144,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
        | k1_funct_1(sK3,X4) = X5 )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f143])).

fof(f160,plain,
    ( ~ spl9_4
    | spl9_20
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f156,f139,f158,f72])).

fof(f156,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4(sK2,X0)) = sK5(sK2,X0)
        | ~ v1_relat_1(sK2)
        | r1_tarski(sK2,X0) )
    | ~ spl9_16 ),
    inference(resolution,[],[f140,f32])).

fof(f145,plain,
    ( spl9_17
    | ~ spl9_11
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f133,f102,f107,f143])).

fof(f133,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,X4) = X5
        | ~ r2_hidden(k4_tarski(X4,X5),sK3) )
    | ~ spl9_10 ),
    inference(resolution,[],[f47,f104])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f141,plain,
    ( spl9_16
    | ~ spl9_4
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f132,f67,f72,f139])).

fof(f132,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK2)
        | k1_funct_1(sK2,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK2) )
    | ~ spl9_3 ),
    inference(resolution,[],[f47,f69])).

fof(f123,plain,
    ( ~ spl9_4
    | spl9_13
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f115,f92,f121,f72])).

fof(f115,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK0)
        | ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_8 ),
    inference(superposition,[],[f44,f94])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f119,plain,
    ( ~ spl9_11
    | spl9_12
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f114,f87,f117,f107])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl9_7 ),
    inference(superposition,[],[f44,f89])).

fof(f110,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f20,f107])).

fof(f20,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_relat_1(X3) )
               => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                    & k1_relat_1(X3) = X0
                    & k1_relat_1(X2) = X0
                    & k2_relat_1(X1) = X0 )
                 => X2 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                  & k1_relat_1(X3) = X0
                  & k1_relat_1(X2) = X0
                  & k2_relat_1(X1) = X0 )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).

fof(f105,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f21,f102])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f100,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f22,f97])).

fof(f22,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f23,f92])).

fof(f23,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f90,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f24,f87])).

fof(f24,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f25,f82])).

fof(f25,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f26,f77])).

fof(f26,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f27,f72])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:16:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (1929)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (1916)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (1934)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (1916)Refutation not found, incomplete strategy% (1916)------------------------------
% 0.21/0.53  % (1916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1916)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1916)Memory used [KB]: 1663
% 0.21/0.53  % (1916)Time elapsed: 0.091 s
% 0.21/0.53  % (1916)------------------------------
% 0.21/0.53  % (1916)------------------------------
% 0.21/0.54  % (1919)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (1921)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.37/0.55  % (1927)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.37/0.55  % (1910)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.54/0.56  % (1928)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.54/0.56  % (1926)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.54/0.56  % (1920)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.54/0.57  % (1932)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.54/0.57  % (1913)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.54/0.57  % (1924)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.54/0.57  % (1915)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.54/0.57  % (1909)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.54/0.58  % (1935)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.54/0.58  % (1933)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.54/0.58  % (1923)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.54/0.58  % (1936)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.54/0.59  % (1917)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.54/0.59  % (1914)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.54/0.59  % (1930)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.54/0.60  % (1908)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.54/0.61  % (1911)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.54/0.62  % (1931)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.54/0.62  % (1922)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.54/0.63  % (1908)Refutation not found, incomplete strategy% (1908)------------------------------
% 1.54/0.63  % (1908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.63  % (1908)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.63  
% 1.54/0.63  % (1908)Memory used [KB]: 10618
% 1.54/0.63  % (1908)Time elapsed: 0.182 s
% 1.54/0.63  % (1908)------------------------------
% 1.54/0.63  % (1908)------------------------------
% 2.92/0.75  % (1919)Refutation not found, incomplete strategy% (1919)------------------------------
% 2.92/0.75  % (1919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.92/0.75  % (1919)Termination reason: Refutation not found, incomplete strategy
% 2.92/0.75  
% 2.92/0.75  % (1919)Memory used [KB]: 6524
% 2.92/0.75  % (1919)Time elapsed: 0.265 s
% 2.92/0.75  % (1919)------------------------------
% 2.92/0.75  % (1919)------------------------------
% 3.03/0.79  % (1926)Refutation found. Thanks to Tanya!
% 3.03/0.79  % SZS status Theorem for theBenchmark
% 3.03/0.79  % SZS output start Proof for theBenchmark
% 3.03/0.80  fof(f3704,plain,(
% 3.03/0.80    $false),
% 3.03/0.80    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f100,f105,f110,f119,f123,f141,f145,f160,f165,f287,f533,f537,f1315,f1348,f1357,f1362,f1395,f1404,f1417,f1422,f1519,f1528,f1633,f2798,f2808,f2883,f3003,f3107,f3132,f3698])).
% 3.03/0.80  fof(f3698,plain,(
% 3.03/0.80    spl9_291 | ~spl9_6 | ~spl9_154 | ~spl9_167 | ~spl9_180 | ~spl9_191 | ~spl9_366),
% 3.03/0.80    inference(avatar_split_clause,[],[f3697,f3129,f1617,f1525,f1414,f1313,f82,f2594])).
% 3.03/0.80  fof(f2594,plain,(
% 3.03/0.80    spl9_291 <=> sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_291])])).
% 3.03/0.80  fof(f82,plain,(
% 3.03/0.80    spl9_6 <=> k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 3.03/0.80  fof(f1313,plain,(
% 3.03/0.80    spl9_154 <=> ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0) | ~r2_hidden(X0,k1_relat_1(sK1)))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).
% 3.03/0.80  fof(f1414,plain,(
% 3.03/0.80    spl9_167 <=> sK5(sK3,sK2) = k1_funct_1(sK3,sK4(sK3,sK2))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_167])])).
% 3.03/0.80  fof(f1525,plain,(
% 3.03/0.80    spl9_180 <=> sK4(sK3,sK2) = k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_180])])).
% 3.03/0.80  fof(f1617,plain,(
% 3.03/0.80    spl9_191 <=> r2_hidden(sK7(sK1,sK4(sK3,sK2)),k1_relat_1(sK1))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_191])])).
% 3.03/0.80  fof(f3129,plain,(
% 3.03/0.80    spl9_366 <=> k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2)))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_366])])).
% 3.03/0.80  fof(f3697,plain,(
% 3.03/0.80    sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) | (~spl9_6 | ~spl9_154 | ~spl9_167 | ~spl9_180 | ~spl9_191 | ~spl9_366)),
% 3.03/0.80    inference(forward_demodulation,[],[f3696,f1416])).
% 3.03/0.80  fof(f1416,plain,(
% 3.03/0.80    sK5(sK3,sK2) = k1_funct_1(sK3,sK4(sK3,sK2)) | ~spl9_167),
% 3.03/0.80    inference(avatar_component_clause,[],[f1414])).
% 3.03/0.80  fof(f3696,plain,(
% 3.03/0.80    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) | (~spl9_6 | ~spl9_154 | ~spl9_180 | ~spl9_191 | ~spl9_366)),
% 3.03/0.80    inference(forward_demodulation,[],[f3695,f1527])).
% 3.03/0.80  fof(f1527,plain,(
% 3.03/0.80    sK4(sK3,sK2) = k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2))) | ~spl9_180),
% 3.03/0.80    inference(avatar_component_clause,[],[f1525])).
% 3.03/0.80  fof(f3695,plain,(
% 3.03/0.80    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))) | (~spl9_6 | ~spl9_154 | ~spl9_191 | ~spl9_366)),
% 3.03/0.80    inference(forward_demodulation,[],[f3673,f3131])).
% 3.03/0.80  fof(f3131,plain,(
% 3.03/0.80    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) | ~spl9_366),
% 3.03/0.80    inference(avatar_component_clause,[],[f3129])).
% 3.03/0.80  fof(f3673,plain,(
% 3.03/0.80    k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) | (~spl9_6 | ~spl9_154 | ~spl9_191)),
% 3.03/0.80    inference(resolution,[],[f1316,f1618])).
% 3.03/0.80  fof(f1618,plain,(
% 3.03/0.80    r2_hidden(sK7(sK1,sK4(sK3,sK2)),k1_relat_1(sK1)) | ~spl9_191),
% 3.03/0.80    inference(avatar_component_clause,[],[f1617])).
% 3.03/0.80  fof(f1316,plain,(
% 3.03/0.80    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)) ) | (~spl9_6 | ~spl9_154)),
% 3.03/0.80    inference(forward_demodulation,[],[f1314,f84])).
% 3.03/0.80  fof(f84,plain,(
% 3.03/0.80    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) | ~spl9_6),
% 3.03/0.80    inference(avatar_component_clause,[],[f82])).
% 3.03/0.80  fof(f1314,plain,(
% 3.03/0.80    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl9_154),
% 3.03/0.80    inference(avatar_component_clause,[],[f1313])).
% 3.03/0.80  fof(f3132,plain,(
% 3.03/0.80    spl9_366 | ~spl9_158 | ~spl9_180 | ~spl9_191),
% 3.03/0.80    inference(avatar_split_clause,[],[f3082,f1617,f1525,f1346,f3129])).
% 3.03/0.80  fof(f1346,plain,(
% 3.03/0.80    spl9_158 <=> ! [X0] : (k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).
% 3.03/0.80  fof(f3082,plain,(
% 3.03/0.80    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) | (~spl9_158 | ~spl9_180 | ~spl9_191)),
% 3.03/0.80    inference(forward_demodulation,[],[f3052,f1527])).
% 3.03/0.80  fof(f3052,plain,(
% 3.03/0.80    k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) = k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))) | (~spl9_158 | ~spl9_191)),
% 3.03/0.80    inference(resolution,[],[f1347,f1618])).
% 3.03/0.80  fof(f1347,plain,(
% 3.03/0.80    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0))) ) | ~spl9_158),
% 3.03/0.80    inference(avatar_component_clause,[],[f1346])).
% 3.03/0.80  fof(f3107,plain,(
% 3.03/0.80    ~spl9_11 | ~spl9_10 | spl9_272 | ~spl9_7 | ~spl9_320),
% 3.03/0.80    inference(avatar_split_clause,[],[f3106,f2806,f87,f2440,f102,f107])).
% 3.03/0.80  fof(f107,plain,(
% 3.03/0.80    spl9_11 <=> v1_relat_1(sK3)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 3.03/0.80  fof(f102,plain,(
% 3.03/0.80    spl9_10 <=> v1_funct_1(sK3)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 3.03/0.80  fof(f2440,plain,(
% 3.03/0.80    spl9_272 <=> ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(sK3,X1) = k1_funct_1(sK2,X1))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_272])])).
% 3.03/0.80  fof(f87,plain,(
% 3.03/0.80    spl9_7 <=> sK0 = k1_relat_1(sK3)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 3.03/0.80  fof(f2806,plain,(
% 3.03/0.80    spl9_320 <=> ! [X3,X2] : (~r2_hidden(k4_tarski(X2,X3),sK3) | k1_funct_1(sK2,X2) = X3)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_320])])).
% 3.03/0.80  fof(f3106,plain,(
% 3.03/0.80    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(sK3,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | (~spl9_7 | ~spl9_320)),
% 3.03/0.80    inference(forward_demodulation,[],[f3100,f89])).
% 3.03/0.80  fof(f89,plain,(
% 3.03/0.80    sK0 = k1_relat_1(sK3) | ~spl9_7),
% 3.03/0.80    inference(avatar_component_clause,[],[f87])).
% 3.03/0.80  fof(f3100,plain,(
% 3.03/0.80    ( ! [X1] : (k1_funct_1(sK3,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(sK3) | ~r2_hidden(X1,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) ) | ~spl9_320),
% 3.03/0.80    inference(resolution,[],[f2807,f55])).
% 3.03/0.80  fof(f55,plain,(
% 3.03/0.80    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.03/0.80    inference(equality_resolution,[],[f48])).
% 3.03/0.80  fof(f48,plain,(
% 3.03/0.80    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 3.03/0.80    inference(cnf_transformation,[],[f19])).
% 3.03/0.80  fof(f19,plain,(
% 3.03/0.80    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.03/0.80    inference(flattening,[],[f18])).
% 3.03/0.80  fof(f18,plain,(
% 3.03/0.80    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.03/0.80    inference(ennf_transformation,[],[f6])).
% 3.03/0.80  fof(f6,axiom,(
% 3.03/0.80    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.03/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 3.03/0.80  fof(f2807,plain,(
% 3.03/0.80    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | k1_funct_1(sK2,X2) = X3) ) | ~spl9_320),
% 3.03/0.80    inference(avatar_component_clause,[],[f2806])).
% 3.03/0.80  fof(f3003,plain,(
% 3.03/0.80    ~spl9_11 | ~spl9_10 | spl9_160 | ~spl9_162 | ~spl9_7 | ~spl9_331),
% 3.03/0.80    inference(avatar_split_clause,[],[f3002,f2880,f87,f1371,f1359,f102,f107])).
% 3.03/0.80  fof(f1359,plain,(
% 3.03/0.80    spl9_160 <=> r2_hidden(k4_tarski(sK4(sK2,sK3),sK5(sK2,sK3)),sK3)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).
% 3.03/0.80  fof(f1371,plain,(
% 3.03/0.80    spl9_162 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).
% 3.03/0.80  fof(f2880,plain,(
% 3.03/0.80    spl9_331 <=> sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_331])])).
% 3.03/0.80  fof(f3002,plain,(
% 3.03/0.80    ~r2_hidden(sK4(sK2,sK3),sK0) | r2_hidden(k4_tarski(sK4(sK2,sK3),sK5(sK2,sK3)),sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl9_7 | ~spl9_331)),
% 3.03/0.80    inference(forward_demodulation,[],[f2995,f89])).
% 3.03/0.80  fof(f2995,plain,(
% 3.03/0.80    r2_hidden(k4_tarski(sK4(sK2,sK3),sK5(sK2,sK3)),sK3) | ~v1_funct_1(sK3) | ~r2_hidden(sK4(sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl9_331),
% 3.03/0.80    inference(superposition,[],[f55,f2882])).
% 3.03/0.80  fof(f2882,plain,(
% 3.03/0.80    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl9_331),
% 3.03/0.80    inference(avatar_component_clause,[],[f2880])).
% 3.03/0.80  fof(f2883,plain,(
% 3.03/0.80    spl9_331 | ~spl9_159 | ~spl9_162 | ~spl9_272),
% 3.03/0.80    inference(avatar_split_clause,[],[f2878,f2440,f1371,f1354,f2880])).
% 3.03/0.80  fof(f1354,plain,(
% 3.03/0.80    spl9_159 <=> k1_funct_1(sK2,sK4(sK2,sK3)) = sK5(sK2,sK3)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_159])])).
% 3.03/0.80  fof(f2878,plain,(
% 3.03/0.80    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl9_159 | ~spl9_162 | ~spl9_272)),
% 3.03/0.80    inference(forward_demodulation,[],[f2823,f1356])).
% 3.03/0.80  fof(f1356,plain,(
% 3.03/0.80    k1_funct_1(sK2,sK4(sK2,sK3)) = sK5(sK2,sK3) | ~spl9_159),
% 3.03/0.80    inference(avatar_component_clause,[],[f1354])).
% 3.03/0.80  fof(f2823,plain,(
% 3.03/0.80    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl9_162 | ~spl9_272)),
% 3.03/0.80    inference(resolution,[],[f1372,f2441])).
% 3.03/0.80  fof(f2441,plain,(
% 3.03/0.80    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(sK3,X1) = k1_funct_1(sK2,X1)) ) | ~spl9_272),
% 3.03/0.80    inference(avatar_component_clause,[],[f2440])).
% 3.03/0.80  fof(f1372,plain,(
% 3.03/0.80    r2_hidden(sK4(sK2,sK3),sK0) | ~spl9_162),
% 3.03/0.80    inference(avatar_component_clause,[],[f1371])).
% 3.03/0.80  fof(f2808,plain,(
% 3.03/0.80    ~spl9_165 | spl9_320 | ~spl9_11 | ~spl9_16),
% 3.03/0.80    inference(avatar_split_clause,[],[f2530,f139,f107,f2806,f1400])).
% 3.03/0.80  fof(f1400,plain,(
% 3.03/0.80    spl9_165 <=> r1_tarski(sK3,sK2)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_165])])).
% 3.03/0.80  fof(f139,plain,(
% 3.03/0.80    spl9_16 <=> ! [X3,X2] : (k1_funct_1(sK2,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK2))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 3.03/0.80  fof(f2530,plain,(
% 3.03/0.80    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | k1_funct_1(sK2,X2) = X3 | ~r1_tarski(sK3,sK2)) ) | (~spl9_11 | ~spl9_16)),
% 3.03/0.80    inference(resolution,[],[f562,f109])).
% 3.03/0.80  fof(f109,plain,(
% 3.03/0.80    v1_relat_1(sK3) | ~spl9_11),
% 3.03/0.80    inference(avatar_component_clause,[],[f107])).
% 3.03/0.80  fof(f562,plain,(
% 3.03/0.80    ( ! [X4,X2,X3] : (~v1_relat_1(X4) | ~r2_hidden(k4_tarski(X2,X3),X4) | k1_funct_1(sK2,X2) = X3 | ~r1_tarski(X4,sK2)) ) | ~spl9_16),
% 3.03/0.80    inference(resolution,[],[f140,f31])).
% 3.03/0.80  fof(f31,plain,(
% 3.03/0.80    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~v1_relat_1(X0) | ~r1_tarski(X0,X1)) )),
% 3.03/0.80    inference(cnf_transformation,[],[f11])).
% 3.03/0.80  fof(f11,plain,(
% 3.03/0.80    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 3.03/0.80    inference(ennf_transformation,[],[f2])).
% 3.03/0.80  fof(f2,axiom,(
% 3.03/0.80    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 3.03/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 3.03/0.80  fof(f140,plain,(
% 3.03/0.80    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3) ) | ~spl9_16),
% 3.03/0.80    inference(avatar_component_clause,[],[f139])).
% 3.03/0.80  fof(f2798,plain,(
% 3.03/0.80    ~spl9_4 | ~spl9_3 | spl9_168 | ~spl9_177 | ~spl9_8 | ~spl9_291),
% 3.03/0.80    inference(avatar_split_clause,[],[f2797,f2594,f92,f1486,f1419,f67,f72])).
% 3.03/0.80  fof(f72,plain,(
% 3.03/0.80    spl9_4 <=> v1_relat_1(sK2)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 3.03/0.80  fof(f67,plain,(
% 3.03/0.80    spl9_3 <=> v1_funct_1(sK2)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 3.03/0.80  fof(f1419,plain,(
% 3.03/0.80    spl9_168 <=> r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_168])])).
% 3.03/0.80  fof(f1486,plain,(
% 3.03/0.80    spl9_177 <=> r2_hidden(sK4(sK3,sK2),sK0)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_177])])).
% 3.03/0.80  fof(f92,plain,(
% 3.03/0.80    spl9_8 <=> sK0 = k1_relat_1(sK2)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 3.03/0.80  fof(f2797,plain,(
% 3.03/0.80    ~r2_hidden(sK4(sK3,sK2),sK0) | r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl9_8 | ~spl9_291)),
% 3.03/0.80    inference(forward_demodulation,[],[f2790,f94])).
% 3.03/0.80  fof(f94,plain,(
% 3.03/0.80    sK0 = k1_relat_1(sK2) | ~spl9_8),
% 3.03/0.80    inference(avatar_component_clause,[],[f92])).
% 3.03/0.80  fof(f2790,plain,(
% 3.03/0.80    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | ~v1_funct_1(sK2) | ~r2_hidden(sK4(sK3,sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl9_291),
% 3.03/0.80    inference(superposition,[],[f55,f2596])).
% 3.03/0.80  fof(f2596,plain,(
% 3.03/0.80    sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) | ~spl9_291),
% 3.03/0.80    inference(avatar_component_clause,[],[f2594])).
% 3.03/0.80  fof(f1633,plain,(
% 3.03/0.80    ~spl9_2 | ~spl9_1 | ~spl9_177 | ~spl9_9 | spl9_191),
% 3.03/0.80    inference(avatar_split_clause,[],[f1632,f1617,f97,f1486,f57,f62])).
% 3.03/0.80  fof(f62,plain,(
% 3.03/0.80    spl9_2 <=> v1_relat_1(sK1)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 3.03/0.80  fof(f57,plain,(
% 3.03/0.80    spl9_1 <=> v1_funct_1(sK1)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 3.03/0.80  fof(f97,plain,(
% 3.03/0.80    spl9_9 <=> sK0 = k2_relat_1(sK1)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 3.03/0.80  fof(f1632,plain,(
% 3.03/0.80    ~r2_hidden(sK4(sK3,sK2),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl9_9 | spl9_191)),
% 3.03/0.80    inference(forward_demodulation,[],[f1630,f99])).
% 3.03/0.80  fof(f99,plain,(
% 3.03/0.80    sK0 = k2_relat_1(sK1) | ~spl9_9),
% 3.03/0.80    inference(avatar_component_clause,[],[f97])).
% 3.03/0.80  fof(f1630,plain,(
% 3.03/0.80    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK4(sK3,sK2),k2_relat_1(sK1)) | spl9_191),
% 3.03/0.80    inference(resolution,[],[f1619,f52])).
% 3.03/0.80  fof(f52,plain,(
% 3.03/0.80    ( ! [X2,X0] : (r2_hidden(sK7(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 3.03/0.80    inference(equality_resolution,[],[f37])).
% 3.03/0.80  fof(f37,plain,(
% 3.03/0.80    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK7(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 3.03/0.80    inference(cnf_transformation,[],[f13])).
% 3.03/0.80  fof(f13,plain,(
% 3.03/0.80    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/0.80    inference(flattening,[],[f12])).
% 3.03/0.80  fof(f12,plain,(
% 3.03/0.80    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/0.80    inference(ennf_transformation,[],[f4])).
% 3.03/0.80  fof(f4,axiom,(
% 3.03/0.80    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.03/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 3.03/0.80  fof(f1619,plain,(
% 3.03/0.80    ~r2_hidden(sK7(sK1,sK4(sK3,sK2)),k1_relat_1(sK1)) | spl9_191),
% 3.03/0.80    inference(avatar_component_clause,[],[f1617])).
% 3.03/0.80  fof(f1528,plain,(
% 3.03/0.80    spl9_180 | ~spl9_37 | ~spl9_177),
% 3.03/0.80    inference(avatar_split_clause,[],[f1522,f1486,f285,f1525])).
% 3.03/0.80  fof(f285,plain,(
% 3.03/0.80    spl9_37 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,sK7(sK1,X0)) = X0)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 3.03/0.80  fof(f1522,plain,(
% 3.03/0.80    sK4(sK3,sK2) = k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2))) | (~spl9_37 | ~spl9_177)),
% 3.03/0.80    inference(resolution,[],[f1487,f286])).
% 3.03/0.80  fof(f286,plain,(
% 3.03/0.80    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,sK7(sK1,X0)) = X0) ) | ~spl9_37),
% 3.03/0.80    inference(avatar_component_clause,[],[f285])).
% 3.03/0.80  fof(f1487,plain,(
% 3.03/0.80    r2_hidden(sK4(sK3,sK2),sK0) | ~spl9_177),
% 3.03/0.80    inference(avatar_component_clause,[],[f1486])).
% 3.03/0.80  fof(f1519,plain,(
% 3.03/0.80    spl9_165 | ~spl9_11 | ~spl9_12 | spl9_177),
% 3.03/0.80    inference(avatar_split_clause,[],[f1515,f1486,f117,f107,f1400])).
% 3.03/0.80  fof(f117,plain,(
% 3.03/0.80    spl9_12 <=> ! [X1,X0] : (r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK3))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 3.03/0.80  fof(f1515,plain,(
% 3.03/0.80    ~v1_relat_1(sK3) | r1_tarski(sK3,sK2) | (~spl9_12 | spl9_177)),
% 3.03/0.80    inference(resolution,[],[f1504,f32])).
% 3.03/0.80  fof(f32,plain,(
% 3.03/0.80    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 3.03/0.80    inference(cnf_transformation,[],[f11])).
% 3.03/0.80  fof(f1504,plain,(
% 3.03/0.80    ( ! [X2] : (~r2_hidden(k4_tarski(sK4(sK3,sK2),X2),sK3)) ) | (~spl9_12 | spl9_177)),
% 3.03/0.80    inference(resolution,[],[f1488,f118])).
% 3.03/0.80  fof(f118,plain,(
% 3.03/0.80    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK3)) ) | ~spl9_12),
% 3.03/0.80    inference(avatar_component_clause,[],[f117])).
% 3.03/0.80  fof(f1488,plain,(
% 3.03/0.80    ~r2_hidden(sK4(sK3,sK2),sK0) | spl9_177),
% 3.03/0.80    inference(avatar_component_clause,[],[f1486])).
% 3.03/0.80  fof(f1422,plain,(
% 3.03/0.80    ~spl9_11 | ~spl9_168 | spl9_165),
% 3.03/0.80    inference(avatar_split_clause,[],[f1407,f1400,f1419,f107])).
% 3.03/0.80  fof(f1407,plain,(
% 3.03/0.80    ~r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | ~v1_relat_1(sK3) | spl9_165),
% 3.03/0.80    inference(resolution,[],[f1402,f33])).
% 3.03/0.80  fof(f33,plain,(
% 3.03/0.80    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 3.03/0.80    inference(cnf_transformation,[],[f11])).
% 3.03/0.80  fof(f1402,plain,(
% 3.03/0.80    ~r1_tarski(sK3,sK2) | spl9_165),
% 3.03/0.80    inference(avatar_component_clause,[],[f1400])).
% 3.03/0.80  fof(f1417,plain,(
% 3.03/0.80    spl9_167 | ~spl9_21 | spl9_165),
% 3.03/0.80    inference(avatar_split_clause,[],[f1406,f1400,f163,f1414])).
% 3.03/0.80  fof(f163,plain,(
% 3.03/0.80    spl9_21 <=> ! [X0] : (k1_funct_1(sK3,sK4(sK3,X0)) = sK5(sK3,X0) | r1_tarski(sK3,X0))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 3.03/0.80  fof(f1406,plain,(
% 3.03/0.80    sK5(sK3,sK2) = k1_funct_1(sK3,sK4(sK3,sK2)) | (~spl9_21 | spl9_165)),
% 3.03/0.80    inference(resolution,[],[f1402,f164])).
% 3.03/0.80  fof(f164,plain,(
% 3.03/0.80    ( ! [X0] : (r1_tarski(sK3,X0) | k1_funct_1(sK3,sK4(sK3,X0)) = sK5(sK3,X0)) ) | ~spl9_21),
% 3.03/0.80    inference(avatar_component_clause,[],[f163])).
% 3.03/0.80  fof(f1404,plain,(
% 3.03/0.80    spl9_5 | ~spl9_165 | ~spl9_156),
% 3.03/0.80    inference(avatar_split_clause,[],[f1398,f1335,f1400,f77])).
% 3.03/0.80  fof(f77,plain,(
% 3.03/0.80    spl9_5 <=> sK2 = sK3),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 3.03/0.80  fof(f1335,plain,(
% 3.03/0.80    spl9_156 <=> r1_tarski(sK2,sK3)),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_156])])).
% 3.03/0.80  fof(f1398,plain,(
% 3.03/0.80    ~r1_tarski(sK3,sK2) | sK2 = sK3 | ~spl9_156),
% 3.03/0.80    inference(resolution,[],[f1336,f43])).
% 3.03/0.80  fof(f43,plain,(
% 3.03/0.80    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.03/0.80    inference(cnf_transformation,[],[f1])).
% 3.03/0.80  fof(f1,axiom,(
% 3.03/0.80    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.03/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.03/0.80  fof(f1336,plain,(
% 3.03/0.80    r1_tarski(sK2,sK3) | ~spl9_156),
% 3.03/0.80    inference(avatar_component_clause,[],[f1335])).
% 3.03/0.80  fof(f1395,plain,(
% 3.03/0.80    spl9_156 | ~spl9_4 | ~spl9_13 | spl9_162),
% 3.03/0.80    inference(avatar_split_clause,[],[f1391,f1371,f121,f72,f1335])).
% 3.03/0.80  fof(f121,plain,(
% 3.03/0.80    spl9_13 <=> ! [X3,X2] : (r2_hidden(X2,sK0) | ~r2_hidden(k4_tarski(X2,X3),sK2))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 3.03/0.80  fof(f1391,plain,(
% 3.03/0.80    ~v1_relat_1(sK2) | r1_tarski(sK2,sK3) | (~spl9_13 | spl9_162)),
% 3.03/0.80    inference(resolution,[],[f1387,f32])).
% 3.03/0.80  fof(f1387,plain,(
% 3.03/0.80    ( ! [X0] : (~r2_hidden(k4_tarski(sK4(sK2,sK3),X0),sK2)) ) | (~spl9_13 | spl9_162)),
% 3.03/0.80    inference(resolution,[],[f1373,f122])).
% 3.03/0.80  fof(f122,plain,(
% 3.03/0.80    ( ! [X2,X3] : (r2_hidden(X2,sK0) | ~r2_hidden(k4_tarski(X2,X3),sK2)) ) | ~spl9_13),
% 3.03/0.80    inference(avatar_component_clause,[],[f121])).
% 3.03/0.80  fof(f1373,plain,(
% 3.03/0.80    ~r2_hidden(sK4(sK2,sK3),sK0) | spl9_162),
% 3.03/0.80    inference(avatar_component_clause,[],[f1371])).
% 3.03/0.80  fof(f1362,plain,(
% 3.03/0.80    ~spl9_4 | ~spl9_160 | spl9_156),
% 3.03/0.80    inference(avatar_split_clause,[],[f1352,f1335,f1359,f72])).
% 3.03/0.80  fof(f1352,plain,(
% 3.03/0.80    ~r2_hidden(k4_tarski(sK4(sK2,sK3),sK5(sK2,sK3)),sK3) | ~v1_relat_1(sK2) | spl9_156),
% 3.03/0.80    inference(resolution,[],[f1337,f33])).
% 3.03/0.80  fof(f1337,plain,(
% 3.03/0.80    ~r1_tarski(sK2,sK3) | spl9_156),
% 3.03/0.80    inference(avatar_component_clause,[],[f1335])).
% 3.03/0.80  fof(f1357,plain,(
% 3.03/0.80    spl9_159 | ~spl9_20 | spl9_156),
% 3.03/0.80    inference(avatar_split_clause,[],[f1351,f1335,f158,f1354])).
% 3.03/0.80  fof(f158,plain,(
% 3.03/0.80    spl9_20 <=> ! [X0] : (k1_funct_1(sK2,sK4(sK2,X0)) = sK5(sK2,X0) | r1_tarski(sK2,X0))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 3.03/0.80  fof(f1351,plain,(
% 3.03/0.80    k1_funct_1(sK2,sK4(sK2,sK3)) = sK5(sK2,sK3) | (~spl9_20 | spl9_156)),
% 3.03/0.80    inference(resolution,[],[f1337,f159])).
% 3.03/0.80  fof(f159,plain,(
% 3.03/0.80    ( ! [X0] : (r1_tarski(sK2,X0) | k1_funct_1(sK2,sK4(sK2,X0)) = sK5(sK2,X0)) ) | ~spl9_20),
% 3.03/0.80    inference(avatar_component_clause,[],[f158])).
% 3.03/0.80  fof(f1348,plain,(
% 3.03/0.80    ~spl9_2 | spl9_158 | ~spl9_1 | ~spl9_65),
% 3.03/0.80    inference(avatar_split_clause,[],[f1342,f535,f57,f1346,f62])).
% 3.03/0.80  fof(f535,plain,(
% 3.03/0.80    spl9_65 <=> ! [X5,X4] : (~v1_funct_1(X4) | k1_funct_1(k5_relat_1(X4,sK2),X5) = k1_funct_1(sK2,k1_funct_1(X4,X5)) | ~r2_hidden(X5,k1_relat_1(X4)) | ~v1_relat_1(X4))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).
% 3.03/0.80  fof(f1342,plain,(
% 3.03/0.80    ( ! [X0] : (k1_funct_1(k5_relat_1(sK1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl9_1 | ~spl9_65)),
% 3.03/0.80    inference(resolution,[],[f536,f59])).
% 3.03/0.80  fof(f59,plain,(
% 3.03/0.80    v1_funct_1(sK1) | ~spl9_1),
% 3.03/0.80    inference(avatar_component_clause,[],[f57])).
% 3.03/0.80  fof(f536,plain,(
% 3.03/0.80    ( ! [X4,X5] : (~v1_funct_1(X4) | k1_funct_1(k5_relat_1(X4,sK2),X5) = k1_funct_1(sK2,k1_funct_1(X4,X5)) | ~r2_hidden(X5,k1_relat_1(X4)) | ~v1_relat_1(X4)) ) | ~spl9_65),
% 3.03/0.80    inference(avatar_component_clause,[],[f535])).
% 3.03/0.80  fof(f1315,plain,(
% 3.03/0.80    ~spl9_2 | spl9_154 | ~spl9_1 | ~spl9_64),
% 3.03/0.80    inference(avatar_split_clause,[],[f1302,f531,f57,f1313,f62])).
% 3.03/0.80  fof(f531,plain,(
% 3.03/0.80    spl9_64 <=> ! [X3,X2] : (~v1_funct_1(X2) | k1_funct_1(k5_relat_1(X2,sK3),X3) = k1_funct_1(sK3,k1_funct_1(X2,X3)) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).
% 3.03/0.80  fof(f1302,plain,(
% 3.03/0.80    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl9_1 | ~spl9_64)),
% 3.03/0.80    inference(resolution,[],[f532,f59])).
% 3.03/0.80  fof(f532,plain,(
% 3.03/0.80    ( ! [X2,X3] : (~v1_funct_1(X2) | k1_funct_1(k5_relat_1(X2,sK3),X3) = k1_funct_1(sK3,k1_funct_1(X2,X3)) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) ) | ~spl9_64),
% 3.03/0.80    inference(avatar_component_clause,[],[f531])).
% 3.03/0.80  fof(f537,plain,(
% 3.03/0.80    ~spl9_4 | spl9_65 | ~spl9_3),
% 3.03/0.80    inference(avatar_split_clause,[],[f520,f67,f535,f72])).
% 3.03/0.80  fof(f520,plain,(
% 3.03/0.80    ( ! [X4,X5] : (~v1_funct_1(X4) | ~v1_relat_1(sK2) | ~v1_relat_1(X4) | ~r2_hidden(X5,k1_relat_1(X4)) | k1_funct_1(k5_relat_1(X4,sK2),X5) = k1_funct_1(sK2,k1_funct_1(X4,X5))) ) | ~spl9_3),
% 3.03/0.80    inference(resolution,[],[f40,f69])).
% 3.03/0.80  fof(f69,plain,(
% 3.03/0.80    v1_funct_1(sK2) | ~spl9_3),
% 3.03/0.80    inference(avatar_component_clause,[],[f67])).
% 3.03/0.80  fof(f40,plain,(
% 3.03/0.80    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 3.03/0.80    inference(cnf_transformation,[],[f15])).
% 3.03/0.80  fof(f15,plain,(
% 3.03/0.80    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.03/0.80    inference(flattening,[],[f14])).
% 3.03/0.80  fof(f14,plain,(
% 3.03/0.80    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.03/0.80    inference(ennf_transformation,[],[f5])).
% 3.03/0.80  fof(f5,axiom,(
% 3.03/0.80    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 3.03/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 3.03/0.80  fof(f533,plain,(
% 3.03/0.80    ~spl9_11 | spl9_64 | ~spl9_10),
% 3.03/0.80    inference(avatar_split_clause,[],[f519,f102,f531,f107])).
% 3.03/0.80  fof(f519,plain,(
% 3.03/0.80    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_relat_1(sK3) | ~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | k1_funct_1(k5_relat_1(X2,sK3),X3) = k1_funct_1(sK3,k1_funct_1(X2,X3))) ) | ~spl9_10),
% 3.03/0.80    inference(resolution,[],[f40,f104])).
% 3.03/0.80  fof(f104,plain,(
% 3.03/0.80    v1_funct_1(sK3) | ~spl9_10),
% 3.03/0.80    inference(avatar_component_clause,[],[f102])).
% 3.03/0.80  fof(f287,plain,(
% 3.03/0.80    ~spl9_2 | spl9_37 | ~spl9_1 | ~spl9_9),
% 3.03/0.80    inference(avatar_split_clause,[],[f283,f97,f57,f285,f62])).
% 3.03/0.80  fof(f283,plain,(
% 3.03/0.80    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK7(sK1,X0)) = X0) ) | (~spl9_1 | ~spl9_9)),
% 3.03/0.80    inference(forward_demodulation,[],[f281,f99])).
% 3.03/0.80  fof(f281,plain,(
% 3.03/0.80    ( ! [X0] : (~v1_relat_1(sK1) | k1_funct_1(sK1,sK7(sK1,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl9_1),
% 3.03/0.80    inference(resolution,[],[f51,f59])).
% 3.03/0.80  fof(f51,plain,(
% 3.03/0.80    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK7(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 3.03/0.80    inference(equality_resolution,[],[f38])).
% 3.03/0.80  fof(f38,plain,(
% 3.03/0.80    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK7(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 3.03/0.80    inference(cnf_transformation,[],[f13])).
% 3.03/0.80  fof(f165,plain,(
% 3.03/0.80    ~spl9_11 | spl9_21 | ~spl9_17),
% 3.03/0.80    inference(avatar_split_clause,[],[f161,f143,f163,f107])).
% 3.03/0.80  fof(f143,plain,(
% 3.03/0.80    spl9_17 <=> ! [X5,X4] : (k1_funct_1(sK3,X4) = X5 | ~r2_hidden(k4_tarski(X4,X5),sK3))),
% 3.03/0.80    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 3.03/0.80  fof(f161,plain,(
% 3.03/0.80    ( ! [X0] : (k1_funct_1(sK3,sK4(sK3,X0)) = sK5(sK3,X0) | ~v1_relat_1(sK3) | r1_tarski(sK3,X0)) ) | ~spl9_17),
% 3.03/0.80    inference(resolution,[],[f144,f32])).
% 3.03/0.80  fof(f144,plain,(
% 3.03/0.80    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK3) | k1_funct_1(sK3,X4) = X5) ) | ~spl9_17),
% 3.03/0.80    inference(avatar_component_clause,[],[f143])).
% 3.03/0.80  fof(f160,plain,(
% 3.03/0.80    ~spl9_4 | spl9_20 | ~spl9_16),
% 3.03/0.80    inference(avatar_split_clause,[],[f156,f139,f158,f72])).
% 3.03/0.80  fof(f156,plain,(
% 3.03/0.80    ( ! [X0] : (k1_funct_1(sK2,sK4(sK2,X0)) = sK5(sK2,X0) | ~v1_relat_1(sK2) | r1_tarski(sK2,X0)) ) | ~spl9_16),
% 3.03/0.80    inference(resolution,[],[f140,f32])).
% 3.03/0.80  fof(f145,plain,(
% 3.03/0.80    spl9_17 | ~spl9_11 | ~spl9_10),
% 3.03/0.80    inference(avatar_split_clause,[],[f133,f102,f107,f143])).
% 3.03/0.80  fof(f133,plain,(
% 3.03/0.80    ( ! [X4,X5] : (~v1_relat_1(sK3) | k1_funct_1(sK3,X4) = X5 | ~r2_hidden(k4_tarski(X4,X5),sK3)) ) | ~spl9_10),
% 3.03/0.80    inference(resolution,[],[f47,f104])).
% 3.03/0.80  fof(f47,plain,(
% 3.03/0.80    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 3.03/0.80    inference(cnf_transformation,[],[f19])).
% 3.03/0.80  fof(f141,plain,(
% 3.03/0.80    spl9_16 | ~spl9_4 | ~spl9_3),
% 3.03/0.80    inference(avatar_split_clause,[],[f132,f67,f72,f139])).
% 3.03/0.80  fof(f132,plain,(
% 3.03/0.80    ( ! [X2,X3] : (~v1_relat_1(sK2) | k1_funct_1(sK2,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK2)) ) | ~spl9_3),
% 3.03/0.80    inference(resolution,[],[f47,f69])).
% 3.03/0.80  fof(f123,plain,(
% 3.03/0.80    ~spl9_4 | spl9_13 | ~spl9_8),
% 3.03/0.80    inference(avatar_split_clause,[],[f115,f92,f121,f72])).
% 3.03/0.80  fof(f115,plain,(
% 3.03/0.80    ( ! [X2,X3] : (r2_hidden(X2,sK0) | ~r2_hidden(k4_tarski(X2,X3),sK2) | ~v1_relat_1(sK2)) ) | ~spl9_8),
% 3.03/0.80    inference(superposition,[],[f44,f94])).
% 3.03/0.80  fof(f44,plain,(
% 3.03/0.80    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.03/0.80    inference(cnf_transformation,[],[f17])).
% 3.03/0.80  fof(f17,plain,(
% 3.03/0.80    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.03/0.80    inference(flattening,[],[f16])).
% 3.03/0.80  fof(f16,plain,(
% 3.03/0.80    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.03/0.80    inference(ennf_transformation,[],[f3])).
% 3.03/0.80  fof(f3,axiom,(
% 3.03/0.80    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.03/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 3.03/0.80  fof(f119,plain,(
% 3.03/0.80    ~spl9_11 | spl9_12 | ~spl9_7),
% 3.03/0.80    inference(avatar_split_clause,[],[f114,f87,f117,f107])).
% 3.03/0.80  fof(f114,plain,(
% 3.03/0.80    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK3) | ~v1_relat_1(sK3)) ) | ~spl9_7),
% 3.03/0.80    inference(superposition,[],[f44,f89])).
% 3.03/0.80  fof(f110,plain,(
% 3.03/0.80    spl9_11),
% 3.03/0.80    inference(avatar_split_clause,[],[f20,f107])).
% 3.03/0.80  fof(f20,plain,(
% 3.03/0.80    v1_relat_1(sK3)),
% 3.03/0.80    inference(cnf_transformation,[],[f10])).
% 3.03/0.80  fof(f10,plain,(
% 3.03/0.80    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.03/0.80    inference(flattening,[],[f9])).
% 3.03/0.80  fof(f9,plain,(
% 3.03/0.80    ? [X0,X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0)) & (v1_funct_1(X3) & v1_relat_1(X3))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.03/0.80    inference(ennf_transformation,[],[f8])).
% 3.03/0.81  fof(f8,negated_conjecture,(
% 3.03/0.81    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 3.03/0.81    inference(negated_conjecture,[],[f7])).
% 3.03/0.81  fof(f7,conjecture,(
% 3.03/0.81    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 3.03/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).
% 3.03/0.81  fof(f105,plain,(
% 3.03/0.81    spl9_10),
% 3.03/0.81    inference(avatar_split_clause,[],[f21,f102])).
% 3.03/0.81  fof(f21,plain,(
% 3.03/0.81    v1_funct_1(sK3)),
% 3.03/0.81    inference(cnf_transformation,[],[f10])).
% 3.03/0.81  fof(f100,plain,(
% 3.03/0.81    spl9_9),
% 3.03/0.81    inference(avatar_split_clause,[],[f22,f97])).
% 3.03/0.81  fof(f22,plain,(
% 3.03/0.81    sK0 = k2_relat_1(sK1)),
% 3.03/0.81    inference(cnf_transformation,[],[f10])).
% 3.03/0.81  fof(f95,plain,(
% 3.03/0.81    spl9_8),
% 3.03/0.81    inference(avatar_split_clause,[],[f23,f92])).
% 3.03/0.81  fof(f23,plain,(
% 3.03/0.81    sK0 = k1_relat_1(sK2)),
% 3.03/0.81    inference(cnf_transformation,[],[f10])).
% 3.03/0.81  fof(f90,plain,(
% 3.03/0.81    spl9_7),
% 3.03/0.81    inference(avatar_split_clause,[],[f24,f87])).
% 3.03/0.81  fof(f24,plain,(
% 3.03/0.81    sK0 = k1_relat_1(sK3)),
% 3.03/0.81    inference(cnf_transformation,[],[f10])).
% 3.03/0.81  fof(f85,plain,(
% 3.03/0.81    spl9_6),
% 3.03/0.81    inference(avatar_split_clause,[],[f25,f82])).
% 3.03/0.81  fof(f25,plain,(
% 3.03/0.81    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)),
% 3.03/0.81    inference(cnf_transformation,[],[f10])).
% 3.03/0.81  fof(f80,plain,(
% 3.03/0.81    ~spl9_5),
% 3.03/0.81    inference(avatar_split_clause,[],[f26,f77])).
% 3.03/0.81  fof(f26,plain,(
% 3.03/0.81    sK2 != sK3),
% 3.03/0.81    inference(cnf_transformation,[],[f10])).
% 3.03/0.81  fof(f75,plain,(
% 3.03/0.81    spl9_4),
% 3.03/0.81    inference(avatar_split_clause,[],[f27,f72])).
% 3.03/0.81  fof(f27,plain,(
% 3.03/0.81    v1_relat_1(sK2)),
% 3.03/0.81    inference(cnf_transformation,[],[f10])).
% 3.03/0.81  fof(f70,plain,(
% 3.03/0.81    spl9_3),
% 3.03/0.81    inference(avatar_split_clause,[],[f28,f67])).
% 3.03/0.81  fof(f28,plain,(
% 3.03/0.81    v1_funct_1(sK2)),
% 3.03/0.81    inference(cnf_transformation,[],[f10])).
% 3.03/0.81  fof(f65,plain,(
% 3.03/0.81    spl9_2),
% 3.03/0.81    inference(avatar_split_clause,[],[f29,f62])).
% 3.03/0.81  fof(f29,plain,(
% 3.03/0.81    v1_relat_1(sK1)),
% 3.03/0.81    inference(cnf_transformation,[],[f10])).
% 3.03/0.81  fof(f60,plain,(
% 3.03/0.81    spl9_1),
% 3.03/0.81    inference(avatar_split_clause,[],[f30,f57])).
% 3.03/0.81  fof(f30,plain,(
% 3.03/0.81    v1_funct_1(sK1)),
% 3.03/0.81    inference(cnf_transformation,[],[f10])).
% 3.03/0.81  % SZS output end Proof for theBenchmark
% 3.03/0.81  % (1926)------------------------------
% 3.03/0.81  % (1926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.81  % (1926)Termination reason: Refutation
% 3.03/0.81  
% 3.03/0.81  % (1926)Memory used [KB]: 9083
% 3.03/0.81  % (1926)Time elapsed: 0.350 s
% 3.03/0.81  % (1926)------------------------------
% 3.03/0.81  % (1926)------------------------------
% 3.51/0.81  % (1903)Success in time 0.45 s
%------------------------------------------------------------------------------
