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
% DateTime   : Thu Dec  3 12:51:02 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 673 expanded)
%              Number of leaves         :   20 ( 229 expanded)
%              Depth                    :   17
%              Number of atoms          :  484 (2945 expanded)
%              Number of equality atoms :  138 ( 697 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1495,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f303,f916,f971,f1026,f1037,f1422,f1426,f1462,f1494])).

fof(f1494,plain,
    ( spl8_1
    | ~ spl8_31
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f1493])).

fof(f1493,plain,
    ( $false
    | spl8_1
    | ~ spl8_31
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f51,f1488])).

fof(f1488,plain,
    ( ! [X14,X15] : X14 = X15
    | ~ spl8_31
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1410,f1417])).

fof(f1417,plain,
    ( ! [X19,X18] :
        ( ~ r2_hidden(k2_relat_1(k1_xboole_0),X18)
        | X18 = X19 )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f1416])).

fof(f1416,plain,
    ( spl8_32
  <=> ! [X18,X19] :
        ( ~ r2_hidden(k2_relat_1(k1_xboole_0),X18)
        | X18 = X19 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f1410,plain,
    ( ! [X14,X15] :
        ( r2_hidden(k2_relat_1(k1_xboole_0),X14)
        | X14 = X15 )
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f1409])).

fof(f1409,plain,
    ( spl8_31
  <=> ! [X15,X14] :
        ( r2_hidden(k2_relat_1(k1_xboole_0),X14)
        | X14 = X15 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f51,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl8_1
  <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1462,plain,
    ( spl8_2
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f1461])).

fof(f1461,plain,
    ( $false
    | spl8_2
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1185,f1438])).

fof(f1438,plain,
    ( ! [X23,X22] : k2_relat_1(X22) = X23
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1437,f1324])).

fof(f1324,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_relat_1(k1_xboole_0),X1)
        | k2_relat_1(X0) = X1 )
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f1323,f999])).

fof(f999,plain,
    ( ! [X2] : k2_relat_1(k1_xboole_0) = X2
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f998])).

fof(f998,plain,
    ( spl8_16
  <=> ! [X2] : k2_relat_1(k1_xboole_0) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f1323,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(X0) = X1
        | r2_hidden(sK2(X0,X1),X1) )
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1094,f1318])).

fof(f1318,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k2_relat_1(k1_xboole_0),X0)
        | k2_relat_1(X0) = X1 )
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1317,f156])).

fof(f156,plain,
    ( ! [X10,X8,X9] :
        ( ~ r2_hidden(X8,X9)
        | r2_hidden(X8,X10) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_5
  <=> ! [X9,X8,X10] :
        ( ~ r2_hidden(X8,X9)
        | r2_hidden(X8,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1317,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k2_relat_1(k1_xboole_0),X1)
        | ~ r2_hidden(k2_relat_1(k1_xboole_0),X0)
        | k2_relat_1(X0) = X1 )
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f1089,f999])).

fof(f1089,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k2_relat_1(k1_xboole_0),X0)
        | k2_relat_1(X0) = X1
        | ~ r2_hidden(sK2(X0,X1),X1) )
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f32,f999])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f14,f13,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1094,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_relat_1(k1_xboole_0),X0)
        | k2_relat_1(X0) = X1
        | r2_hidden(sK2(X0,X1),X1) )
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f31,f999])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1437,plain,
    ( ! [X23,X22] :
        ( ~ r2_hidden(k2_relat_1(k1_xboole_0),X23)
        | k2_relat_1(X22) = X23 )
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f1436,f999])).

fof(f1436,plain,
    ( ! [X23,X22] :
        ( k2_relat_1(X22) = X23
        | ~ r2_hidden(sK2(X22,X23),X23) )
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1161,f156])).

fof(f1161,plain,
    ( ! [X23,X22] :
        ( ~ r2_hidden(sK2(X22,X23),k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0))))
        | k2_relat_1(X22) = X23
        | ~ r2_hidden(sK2(X22,X23),X23) )
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f872,f999])).

fof(f872,plain,(
    ! [X24,X23,X22] :
      ( ~ r2_hidden(sK2(X22,X23),k2_relat_1(k2_relat_1(k2_zfmisc_1(X24,X22))))
      | k2_relat_1(X22) = X23
      | ~ r2_hidden(sK2(X22,X23),X23) ) ),
    inference(resolution,[],[f118,f32])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(k2_relat_1(k2_zfmisc_1(X0,X1)),X2),X2),X1)
      | ~ r2_hidden(X2,k2_relat_1(k2_relat_1(k2_zfmisc_1(X0,X1)))) ) ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,k2_relat_1(k2_zfmisc_1(X5,X6)))
      | r2_hidden(X4,X6) ) ),
    inference(resolution,[],[f44,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f1185,plain,
    ( sK1 != k2_relat_1(k2_relat_1(k1_xboole_0))
    | spl8_2
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f54,f999])).

fof(f54,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl8_2
  <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1426,plain,
    ( spl8_3
    | spl8_32
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f1425,f998,f155,f1416,f148])).

fof(f148,plain,
    ( spl8_3
  <=> ! [X1,X2] : ~ r2_hidden(X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1425,plain,
    ( ! [X30,X33,X31,X32] :
        ( ~ r2_hidden(k2_relat_1(k1_xboole_0),X30)
        | X30 = X32
        | ~ r2_hidden(X33,X31) )
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1424,f156])).

fof(f1424,plain,
    ( ! [X30,X33,X31,X32] :
        ( ~ r2_hidden(k2_relat_1(k1_xboole_0),X32)
        | ~ r2_hidden(k2_relat_1(k1_xboole_0),X30)
        | X30 = X32
        | ~ r2_hidden(X33,X31) )
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f1423,f999])).

fof(f1423,plain,
    ( ! [X30,X33,X31,X32] :
        ( ~ r2_hidden(k2_relat_1(k1_xboole_0),X30)
        | ~ r2_hidden(sK5(k2_zfmisc_1(X30,X31),X32),X32)
        | X30 = X32
        | ~ r2_hidden(X33,X31) )
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f1156,f999])).

fof(f1156,plain,
    ( ! [X30,X33,X31,X32] :
        ( ~ r2_hidden(sK5(k2_relat_1(k1_xboole_0),X32),X30)
        | ~ r2_hidden(sK5(k2_zfmisc_1(X30,X31),X32),X32)
        | X30 = X32
        | ~ r2_hidden(X33,X31) )
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f852,f999])).

fof(f852,plain,(
    ! [X30,X33,X31,X32] :
      ( ~ r2_hidden(sK5(k2_zfmisc_1(X30,X31),X32),X30)
      | ~ r2_hidden(sK5(k2_zfmisc_1(X30,X31),X32),X32)
      | X30 = X32
      | ~ r2_hidden(X33,X31) ) ),
    inference(superposition,[],[f84,f804])).

fof(f804,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | ~ r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f803,f420])).

fof(f420,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k2_zfmisc_1(X0,X1),X0),X0)
      | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 ) ),
    inference(factoring,[],[f103])).

fof(f103,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(sK5(k2_zfmisc_1(X9,X10),X11),X11)
      | k1_relat_1(k2_zfmisc_1(X9,X10)) = X11
      | r2_hidden(sK5(k2_zfmisc_1(X9,X10),X11),X9) ) ),
    inference(resolution,[],[f35,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f17,f20,f19,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f803,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(sK5(k2_zfmisc_1(X0,X1),X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f797])).

fof(f797,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(sK5(k2_zfmisc_1(X0,X1),X0),X0) ) ),
    inference(resolution,[],[f420,f85])).

fof(f85,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK5(k2_zfmisc_1(X2,X3),X4),X4)
      | k1_relat_1(k2_zfmisc_1(X2,X3)) = X4
      | ~ r2_hidden(X5,X3)
      | ~ r2_hidden(sK5(k2_zfmisc_1(X2,X3),X4),X2) ) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
      | k1_relat_1(X0) = X1
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f36,f46])).

fof(f46,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1422,plain,
    ( spl8_3
    | spl8_31
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f1421,f998,f155,f1409,f148])).

fof(f1421,plain,
    ( ! [X24,X23,X25,X22] :
        ( r2_hidden(k2_relat_1(k1_xboole_0),X22)
        | X22 = X24
        | ~ r2_hidden(X25,X23) )
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1420,f156])).

fof(f1420,plain,
    ( ! [X24,X23,X25,X22] :
        ( r2_hidden(k2_relat_1(k1_xboole_0),X24)
        | r2_hidden(k2_relat_1(k1_xboole_0),X22)
        | X22 = X24
        | ~ r2_hidden(X25,X23) )
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f1419,f999])).

fof(f1419,plain,
    ( ! [X24,X23,X25,X22] :
        ( r2_hidden(k2_relat_1(k1_xboole_0),X22)
        | r2_hidden(sK5(k2_zfmisc_1(X22,X23),X24),X24)
        | X22 = X24
        | ~ r2_hidden(X25,X23) )
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f1155,f999])).

fof(f1155,plain,
    ( ! [X24,X23,X25,X22] :
        ( r2_hidden(sK5(k2_relat_1(k1_xboole_0),X24),X22)
        | r2_hidden(sK5(k2_zfmisc_1(X22,X23),X24),X24)
        | X22 = X24
        | ~ r2_hidden(X25,X23) )
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f850,f999])).

fof(f850,plain,(
    ! [X24,X23,X25,X22] :
      ( r2_hidden(sK5(k2_zfmisc_1(X22,X23),X24),X22)
      | r2_hidden(sK5(k2_zfmisc_1(X22,X23),X24),X24)
      | X22 = X24
      | ~ r2_hidden(X25,X23) ) ),
    inference(superposition,[],[f100,f804])).

fof(f100,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3),k1_relat_1(X2))
      | r2_hidden(sK5(X2,X3),X3)
      | k1_relat_1(X2) = X3 ) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1037,plain,
    ( spl8_16
    | spl8_6 ),
    inference(avatar_split_clause,[],[f1036,f158,f998])).

fof(f158,plain,
    ( spl8_6
  <=> ! [X7] : ~ r2_hidden(X7,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1036,plain,(
    ! [X19,X17] :
      ( ~ r2_hidden(X19,k1_xboole_0)
      | k2_relat_1(k1_xboole_0) = X17 ) ),
    inference(global_subsumption,[],[f1022])).

fof(f1022,plain,(
    ! [X4,X5] :
      ( k2_relat_1(k1_xboole_0) = X4
      | ~ r2_hidden(X5,k1_xboole_0) ) ),
    inference(global_subsumption,[],[f817])).

fof(f817,plain,(
    ! [X2,X3] :
      ( k2_relat_1(k1_xboole_0) = X2
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f496,f48])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f496,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f495,f366])).

fof(f366,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k2_zfmisc_1(X0,X1),X1),X1)
      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 ) ),
    inference(factoring,[],[f89])).

fof(f89,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK2(k2_zfmisc_1(X6,X7),X8),X8)
      | k2_relat_1(k2_zfmisc_1(X6,X7)) = X8
      | r2_hidden(sK2(k2_zfmisc_1(X6,X7),X8),X7) ) ),
    inference(resolution,[],[f31,f41])).

fof(f495,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | ~ r2_hidden(sK2(k2_zfmisc_1(X0,X1),X1),X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f480])).

fof(f480,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | ~ r2_hidden(sK2(k2_zfmisc_1(X0,X1),X1),X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f366,f81])).

fof(f81,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK2(k2_zfmisc_1(X2,X3),X4),X4)
      | k2_relat_1(k2_zfmisc_1(X2,X3)) = X4
      | ~ r2_hidden(sK2(k2_zfmisc_1(X2,X3),X4),X3)
      | ~ r2_hidden(X5,X2) ) ),
    inference(resolution,[],[f32,f42])).

fof(f1026,plain,
    ( spl8_6
    | spl8_5 ),
    inference(avatar_split_clause,[],[f179,f155,f158])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X0,X3) ) ),
    inference(resolution,[],[f79,f59])).

fof(f59,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k1_xboole_0)
      | r2_hidden(X5,X3) ) ),
    inference(superposition,[],[f41,f48])).

fof(f79,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k4_tarski(X4,X5),k1_xboole_0)
      | ~ r2_hidden(X5,X3)
      | ~ r2_hidden(X4,k1_xboole_0) ) ),
    inference(superposition,[],[f42,f48])).

fof(f971,plain,
    ( spl8_2
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f970])).

fof(f970,plain,
    ( $false
    | spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f964,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
      | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
          | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
        | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f964,plain,
    ( k1_xboole_0 = sK0
    | spl8_2
    | ~ spl8_6 ),
    inference(resolution,[],[f918,f679])).

fof(f679,plain,
    ( ! [X12] :
        ( r2_hidden(sK5(k1_xboole_0,X12),X12)
        | k1_xboole_0 = X12 )
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f631,f159])).

fof(f159,plain,
    ( ! [X7] : ~ r2_hidden(X7,k1_xboole_0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f158])).

fof(f631,plain,
    ( ! [X12] :
        ( k1_xboole_0 = X12
        | r2_hidden(sK5(k1_xboole_0,X12),X12)
        | r2_hidden(sK6(k1_xboole_0,X12),k1_xboole_0) )
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f104,f621])).

fof(f621,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_6 ),
    inference(resolution,[],[f540,f305])).

fof(f305,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_relat_1(k1_xboole_0))
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f233,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f233,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k1_relat_1(k2_zfmisc_1(X4,k1_xboole_0)))
    | ~ spl8_6 ),
    inference(resolution,[],[f69,f159])).

fof(f69,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK7(k2_zfmisc_1(X5,X6),X4),X6)
      | ~ r2_hidden(X4,k1_relat_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f46,f41])).

fof(f540,plain,
    ( ! [X12] :
        ( r2_hidden(sK2(k1_xboole_0,X12),X12)
        | k1_xboole_0 = X12 )
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f500,f159])).

fof(f500,plain,
    ( ! [X12] :
        ( k1_xboole_0 = X12
        | r2_hidden(sK2(k1_xboole_0,X12),X12)
        | r2_hidden(sK2(k1_xboole_0,X12),k1_xboole_0) )
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f91,f497])).

fof(f497,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f481,f47])).

fof(f481,plain,
    ( ! [X3] : k1_xboole_0 = k2_relat_1(k2_zfmisc_1(X3,k1_xboole_0))
    | ~ spl8_6 ),
    inference(resolution,[],[f366,f159])).

fof(f91,plain,(
    ! [X12] :
      ( k2_relat_1(k1_xboole_0) = X12
      | r2_hidden(sK2(k1_xboole_0,X12),X12)
      | r2_hidden(sK2(k1_xboole_0,X12),k1_xboole_0) ) ),
    inference(resolution,[],[f31,f58])).

fof(f58,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0)
      | r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f41,f47])).

fof(f104,plain,(
    ! [X12] :
      ( k1_relat_1(k1_xboole_0) = X12
      | r2_hidden(sK5(k1_xboole_0,X12),X12)
      | r2_hidden(sK6(k1_xboole_0,X12),k1_xboole_0) ) ),
    inference(resolution,[],[f35,f58])).

fof(f918,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl8_2 ),
    inference(trivial_inequality_removal,[],[f917])).

fof(f917,plain,
    ( ! [X0] :
        ( sK1 != sK1
        | ~ r2_hidden(X0,sK0) )
    | spl8_2 ),
    inference(superposition,[],[f54,f496])).

fof(f916,plain,
    ( spl8_1
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f915])).

fof(f915,plain,
    ( $false
    | spl8_1
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f909,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f909,plain,
    ( k1_xboole_0 = sK1
    | spl8_1
    | ~ spl8_6 ),
    inference(resolution,[],[f854,f679])).

fof(f854,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | spl8_1 ),
    inference(trivial_inequality_removal,[],[f845])).

fof(f845,plain,
    ( ! [X0] :
        ( sK0 != sK0
        | ~ r2_hidden(X0,sK1) )
    | spl8_1 ),
    inference(superposition,[],[f51,f804])).

fof(f303,plain,
    ( spl8_1
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f277,f197])).

fof(f197,plain,
    ( ! [X2,X3] : k2_relat_1(X2) = X3
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f187,f149])).

fof(f149,plain,
    ( ! [X2,X1] : ~ r2_hidden(X1,X2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f148])).

fof(f187,plain,
    ( ! [X2,X3] :
        ( k2_relat_1(X2) = X3
        | r2_hidden(sK2(X2,X3),X3) )
    | ~ spl8_3 ),
    inference(resolution,[],[f149,f31])).

fof(f277,plain,
    ( ! [X0] : k2_relat_1(X0) != sK0
    | spl8_1
    | ~ spl8_3 ),
    inference(superposition,[],[f51,f197])).

fof(f55,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f28,f53,f50])).

fof(f28,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:24:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (26210)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  % (26212)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (26212)Refutation not found, incomplete strategy% (26212)------------------------------
% 0.22/0.47  % (26212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26212)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (26212)Memory used [KB]: 1663
% 0.22/0.47  % (26212)Time elapsed: 0.051 s
% 0.22/0.47  % (26212)------------------------------
% 0.22/0.47  % (26212)------------------------------
% 0.22/0.47  % (26204)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (26218)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (26208)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (26203)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (26213)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (26216)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (26205)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (26214)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (26211)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (26211)Refutation not found, incomplete strategy% (26211)------------------------------
% 0.22/0.50  % (26211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26211)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26211)Memory used [KB]: 6012
% 0.22/0.50  % (26211)Time elapsed: 0.001 s
% 0.22/0.50  % (26211)------------------------------
% 0.22/0.50  % (26211)------------------------------
% 0.22/0.51  % (26219)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (26199)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (26219)Refutation not found, incomplete strategy% (26219)------------------------------
% 0.22/0.51  % (26219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26219)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26219)Memory used [KB]: 10618
% 0.22/0.51  % (26219)Time elapsed: 0.097 s
% 0.22/0.51  % (26219)------------------------------
% 0.22/0.51  % (26219)------------------------------
% 0.22/0.51  % (26199)Refutation not found, incomplete strategy% (26199)------------------------------
% 0.22/0.51  % (26199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26199)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26199)Memory used [KB]: 6140
% 0.22/0.51  % (26199)Time elapsed: 0.067 s
% 0.22/0.51  % (26199)------------------------------
% 0.22/0.51  % (26199)------------------------------
% 1.24/0.51  % (26206)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.24/0.51  % (26202)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.52  % (26202)Refutation not found, incomplete strategy% (26202)------------------------------
% 1.24/0.52  % (26202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (26202)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (26202)Memory used [KB]: 10618
% 1.24/0.52  % (26202)Time elapsed: 0.091 s
% 1.24/0.52  % (26202)------------------------------
% 1.24/0.52  % (26202)------------------------------
% 1.24/0.52  % (26200)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.52  % (26215)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.24/0.52  % (26200)Refutation not found, incomplete strategy% (26200)------------------------------
% 1.24/0.52  % (26200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (26200)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (26200)Memory used [KB]: 10618
% 1.24/0.52  % (26200)Time elapsed: 0.102 s
% 1.24/0.52  % (26200)------------------------------
% 1.24/0.52  % (26200)------------------------------
% 1.24/0.52  % (26207)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.24/0.52  % (26217)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.24/0.52  % (26201)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.24/0.53  % (26209)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.39/0.57  % (26201)Refutation found. Thanks to Tanya!
% 1.39/0.57  % SZS status Theorem for theBenchmark
% 1.39/0.57  % SZS output start Proof for theBenchmark
% 1.39/0.57  fof(f1495,plain,(
% 1.39/0.57    $false),
% 1.39/0.57    inference(avatar_sat_refutation,[],[f55,f303,f916,f971,f1026,f1037,f1422,f1426,f1462,f1494])).
% 1.39/0.57  fof(f1494,plain,(
% 1.39/0.57    spl8_1 | ~spl8_31 | ~spl8_32),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f1493])).
% 1.39/0.57  fof(f1493,plain,(
% 1.39/0.57    $false | (spl8_1 | ~spl8_31 | ~spl8_32)),
% 1.39/0.57    inference(subsumption_resolution,[],[f51,f1488])).
% 1.39/0.57  fof(f1488,plain,(
% 1.39/0.57    ( ! [X14,X15] : (X14 = X15) ) | (~spl8_31 | ~spl8_32)),
% 1.39/0.57    inference(subsumption_resolution,[],[f1410,f1417])).
% 1.39/0.57  fof(f1417,plain,(
% 1.39/0.57    ( ! [X19,X18] : (~r2_hidden(k2_relat_1(k1_xboole_0),X18) | X18 = X19) ) | ~spl8_32),
% 1.39/0.57    inference(avatar_component_clause,[],[f1416])).
% 1.39/0.57  fof(f1416,plain,(
% 1.39/0.57    spl8_32 <=> ! [X18,X19] : (~r2_hidden(k2_relat_1(k1_xboole_0),X18) | X18 = X19)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.39/0.57  fof(f1410,plain,(
% 1.39/0.57    ( ! [X14,X15] : (r2_hidden(k2_relat_1(k1_xboole_0),X14) | X14 = X15) ) | ~spl8_31),
% 1.39/0.57    inference(avatar_component_clause,[],[f1409])).
% 1.39/0.57  fof(f1409,plain,(
% 1.39/0.57    spl8_31 <=> ! [X15,X14] : (r2_hidden(k2_relat_1(k1_xboole_0),X14) | X14 = X15)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 1.39/0.57  fof(f51,plain,(
% 1.39/0.57    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl8_1),
% 1.39/0.57    inference(avatar_component_clause,[],[f50])).
% 1.39/0.57  fof(f50,plain,(
% 1.39/0.57    spl8_1 <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.39/0.57  fof(f1462,plain,(
% 1.39/0.57    spl8_2 | ~spl8_5 | ~spl8_16),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f1461])).
% 1.39/0.57  fof(f1461,plain,(
% 1.39/0.57    $false | (spl8_2 | ~spl8_5 | ~spl8_16)),
% 1.39/0.57    inference(subsumption_resolution,[],[f1185,f1438])).
% 1.39/0.57  fof(f1438,plain,(
% 1.39/0.57    ( ! [X23,X22] : (k2_relat_1(X22) = X23) ) | (~spl8_5 | ~spl8_16)),
% 1.39/0.57    inference(subsumption_resolution,[],[f1437,f1324])).
% 1.39/0.57  fof(f1324,plain,(
% 1.39/0.57    ( ! [X0,X1] : (r2_hidden(k2_relat_1(k1_xboole_0),X1) | k2_relat_1(X0) = X1) ) | (~spl8_5 | ~spl8_16)),
% 1.39/0.57    inference(forward_demodulation,[],[f1323,f999])).
% 1.39/0.57  fof(f999,plain,(
% 1.39/0.57    ( ! [X2] : (k2_relat_1(k1_xboole_0) = X2) ) | ~spl8_16),
% 1.39/0.57    inference(avatar_component_clause,[],[f998])).
% 1.39/0.57  fof(f998,plain,(
% 1.39/0.57    spl8_16 <=> ! [X2] : k2_relat_1(k1_xboole_0) = X2),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.39/0.57  fof(f1323,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X1)) ) | (~spl8_5 | ~spl8_16)),
% 1.39/0.57    inference(subsumption_resolution,[],[f1094,f1318])).
% 1.39/0.57  fof(f1318,plain,(
% 1.39/0.57    ( ! [X0,X1] : (~r2_hidden(k2_relat_1(k1_xboole_0),X0) | k2_relat_1(X0) = X1) ) | (~spl8_5 | ~spl8_16)),
% 1.39/0.57    inference(subsumption_resolution,[],[f1317,f156])).
% 1.39/0.57  fof(f156,plain,(
% 1.39/0.57    ( ! [X10,X8,X9] : (~r2_hidden(X8,X9) | r2_hidden(X8,X10)) ) | ~spl8_5),
% 1.39/0.57    inference(avatar_component_clause,[],[f155])).
% 1.39/0.57  fof(f155,plain,(
% 1.39/0.57    spl8_5 <=> ! [X9,X8,X10] : (~r2_hidden(X8,X9) | r2_hidden(X8,X10))),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.39/0.57  fof(f1317,plain,(
% 1.39/0.57    ( ! [X0,X1] : (~r2_hidden(k2_relat_1(k1_xboole_0),X1) | ~r2_hidden(k2_relat_1(k1_xboole_0),X0) | k2_relat_1(X0) = X1) ) | ~spl8_16),
% 1.39/0.57    inference(forward_demodulation,[],[f1089,f999])).
% 1.39/0.57  fof(f1089,plain,(
% 1.39/0.57    ( ! [X0,X1] : (~r2_hidden(k2_relat_1(k1_xboole_0),X0) | k2_relat_1(X0) = X1 | ~r2_hidden(sK2(X0,X1),X1)) ) | ~spl8_16),
% 1.39/0.57    inference(backward_demodulation,[],[f32,f999])).
% 1.39/0.57  fof(f32,plain,(
% 1.39/0.57    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | k2_relat_1(X0) = X1 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f15])).
% 1.39/0.57  fof(f15,plain,(
% 1.39/0.57    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.39/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f14,f13,f12])).
% 1.39/0.57  fof(f12,plain,(
% 1.39/0.57    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.39/0.57    introduced(choice_axiom,[])).
% 1.39/0.59  fof(f13,plain,(
% 1.39/0.59    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0))),
% 1.39/0.59    introduced(choice_axiom,[])).
% 1.39/0.59  fof(f14,plain,(
% 1.39/0.59    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 1.39/0.59    introduced(choice_axiom,[])).
% 1.39/0.59  fof(f11,plain,(
% 1.39/0.59    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.39/0.59    inference(rectify,[],[f10])).
% 1.39/0.59  fof(f10,plain,(
% 1.39/0.59    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.39/0.59    inference(nnf_transformation,[],[f4])).
% 1.39/0.59  fof(f4,axiom,(
% 1.39/0.59    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.39/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.39/0.59  fof(f1094,plain,(
% 1.39/0.59    ( ! [X0,X1] : (r2_hidden(k2_relat_1(k1_xboole_0),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X1)) ) | ~spl8_16),
% 1.39/0.59    inference(backward_demodulation,[],[f31,f999])).
% 1.39/0.59  fof(f31,plain,(
% 1.39/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f15])).
% 1.39/0.59  fof(f1437,plain,(
% 1.39/0.59    ( ! [X23,X22] : (~r2_hidden(k2_relat_1(k1_xboole_0),X23) | k2_relat_1(X22) = X23) ) | (~spl8_5 | ~spl8_16)),
% 1.39/0.59    inference(forward_demodulation,[],[f1436,f999])).
% 1.39/0.59  fof(f1436,plain,(
% 1.39/0.59    ( ! [X23,X22] : (k2_relat_1(X22) = X23 | ~r2_hidden(sK2(X22,X23),X23)) ) | (~spl8_5 | ~spl8_16)),
% 1.39/0.59    inference(subsumption_resolution,[],[f1161,f156])).
% 1.39/0.59  fof(f1161,plain,(
% 1.39/0.59    ( ! [X23,X22] : (~r2_hidden(sK2(X22,X23),k2_relat_1(k2_relat_1(k2_relat_1(k1_xboole_0)))) | k2_relat_1(X22) = X23 | ~r2_hidden(sK2(X22,X23),X23)) ) | ~spl8_16),
% 1.39/0.59    inference(backward_demodulation,[],[f872,f999])).
% 1.39/0.59  fof(f872,plain,(
% 1.39/0.59    ( ! [X24,X23,X22] : (~r2_hidden(sK2(X22,X23),k2_relat_1(k2_relat_1(k2_zfmisc_1(X24,X22)))) | k2_relat_1(X22) = X23 | ~r2_hidden(sK2(X22,X23),X23)) )),
% 1.39/0.59    inference(resolution,[],[f118,f32])).
% 1.39/0.59  fof(f118,plain,(
% 1.39/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(k2_relat_1(k2_zfmisc_1(X0,X1)),X2),X2),X1) | ~r2_hidden(X2,k2_relat_1(k2_relat_1(k2_zfmisc_1(X0,X1))))) )),
% 1.39/0.59    inference(resolution,[],[f64,f44])).
% 1.39/0.59  fof(f44,plain,(
% 1.39/0.59    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.39/0.59    inference(equality_resolution,[],[f29])).
% 1.39/0.59  fof(f29,plain,(
% 1.39/0.59    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.39/0.59    inference(cnf_transformation,[],[f15])).
% 1.39/0.59  fof(f64,plain,(
% 1.39/0.59    ( ! [X6,X4,X5] : (~r2_hidden(X4,k2_relat_1(k2_zfmisc_1(X5,X6))) | r2_hidden(X4,X6)) )),
% 1.39/0.59    inference(resolution,[],[f44,f41])).
% 1.39/0.59  fof(f41,plain,(
% 1.39/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f25])).
% 1.39/0.59  fof(f25,plain,(
% 1.39/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.39/0.59    inference(flattening,[],[f24])).
% 1.39/0.59  fof(f24,plain,(
% 1.39/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.39/0.59    inference(nnf_transformation,[],[f1])).
% 1.39/0.59  fof(f1,axiom,(
% 1.39/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.39/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.39/0.59  fof(f1185,plain,(
% 1.39/0.59    sK1 != k2_relat_1(k2_relat_1(k1_xboole_0)) | (spl8_2 | ~spl8_16)),
% 1.39/0.59    inference(backward_demodulation,[],[f54,f999])).
% 1.39/0.59  fof(f54,plain,(
% 1.39/0.59    sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | spl8_2),
% 1.39/0.59    inference(avatar_component_clause,[],[f53])).
% 1.39/0.59  fof(f53,plain,(
% 1.39/0.59    spl8_2 <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.39/0.59  fof(f1426,plain,(
% 1.39/0.59    spl8_3 | spl8_32 | ~spl8_5 | ~spl8_16),
% 1.39/0.59    inference(avatar_split_clause,[],[f1425,f998,f155,f1416,f148])).
% 1.39/0.59  fof(f148,plain,(
% 1.39/0.59    spl8_3 <=> ! [X1,X2] : ~r2_hidden(X1,X2)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.39/0.59  fof(f1425,plain,(
% 1.39/0.59    ( ! [X30,X33,X31,X32] : (~r2_hidden(k2_relat_1(k1_xboole_0),X30) | X30 = X32 | ~r2_hidden(X33,X31)) ) | (~spl8_5 | ~spl8_16)),
% 1.39/0.59    inference(subsumption_resolution,[],[f1424,f156])).
% 1.39/0.59  fof(f1424,plain,(
% 1.39/0.59    ( ! [X30,X33,X31,X32] : (~r2_hidden(k2_relat_1(k1_xboole_0),X32) | ~r2_hidden(k2_relat_1(k1_xboole_0),X30) | X30 = X32 | ~r2_hidden(X33,X31)) ) | ~spl8_16),
% 1.39/0.59    inference(forward_demodulation,[],[f1423,f999])).
% 1.39/0.59  fof(f1423,plain,(
% 1.39/0.59    ( ! [X30,X33,X31,X32] : (~r2_hidden(k2_relat_1(k1_xboole_0),X30) | ~r2_hidden(sK5(k2_zfmisc_1(X30,X31),X32),X32) | X30 = X32 | ~r2_hidden(X33,X31)) ) | ~spl8_16),
% 1.39/0.59    inference(forward_demodulation,[],[f1156,f999])).
% 1.39/0.59  fof(f1156,plain,(
% 1.39/0.59    ( ! [X30,X33,X31,X32] : (~r2_hidden(sK5(k2_relat_1(k1_xboole_0),X32),X30) | ~r2_hidden(sK5(k2_zfmisc_1(X30,X31),X32),X32) | X30 = X32 | ~r2_hidden(X33,X31)) ) | ~spl8_16),
% 1.39/0.59    inference(backward_demodulation,[],[f852,f999])).
% 1.39/0.59  fof(f852,plain,(
% 1.39/0.59    ( ! [X30,X33,X31,X32] : (~r2_hidden(sK5(k2_zfmisc_1(X30,X31),X32),X30) | ~r2_hidden(sK5(k2_zfmisc_1(X30,X31),X32),X32) | X30 = X32 | ~r2_hidden(X33,X31)) )),
% 1.39/0.59    inference(superposition,[],[f84,f804])).
% 1.39/0.59  fof(f804,plain,(
% 1.39/0.59    ( ! [X2,X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | ~r2_hidden(X2,X1)) )),
% 1.39/0.59    inference(subsumption_resolution,[],[f803,f420])).
% 1.39/0.59  fof(f420,plain,(
% 1.39/0.59    ( ! [X0,X1] : (r2_hidden(sK5(k2_zfmisc_1(X0,X1),X0),X0) | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) )),
% 1.39/0.59    inference(factoring,[],[f103])).
% 1.39/0.59  fof(f103,plain,(
% 1.39/0.59    ( ! [X10,X11,X9] : (r2_hidden(sK5(k2_zfmisc_1(X9,X10),X11),X11) | k1_relat_1(k2_zfmisc_1(X9,X10)) = X11 | r2_hidden(sK5(k2_zfmisc_1(X9,X10),X11),X9)) )),
% 1.39/0.59    inference(resolution,[],[f35,f40])).
% 1.39/0.59  fof(f40,plain,(
% 1.39/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f25])).
% 1.39/0.59  fof(f35,plain,(
% 1.39/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK5(X0,X1),X1)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f21])).
% 1.39/0.59  fof(f21,plain,(
% 1.39/0.59    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.39/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f17,f20,f19,f18])).
% 1.39/0.59  fof(f18,plain,(
% 1.39/0.59    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 1.39/0.59    introduced(choice_axiom,[])).
% 1.39/0.59  fof(f19,plain,(
% 1.39/0.59    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 1.39/0.59    introduced(choice_axiom,[])).
% 1.39/0.59  fof(f20,plain,(
% 1.39/0.59    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 1.39/0.59    introduced(choice_axiom,[])).
% 1.39/0.59  fof(f17,plain,(
% 1.39/0.59    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.39/0.59    inference(rectify,[],[f16])).
% 1.39/0.59  fof(f16,plain,(
% 1.39/0.59    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.39/0.59    inference(nnf_transformation,[],[f3])).
% 1.39/0.59  fof(f3,axiom,(
% 1.39/0.59    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.39/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.39/0.59  fof(f803,plain,(
% 1.39/0.59    ( ! [X2,X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | ~r2_hidden(X2,X1) | ~r2_hidden(sK5(k2_zfmisc_1(X0,X1),X0),X0)) )),
% 1.39/0.59    inference(duplicate_literal_removal,[],[f797])).
% 1.39/0.59  fof(f797,plain,(
% 1.39/0.59    ( ! [X2,X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | ~r2_hidden(X2,X1) | ~r2_hidden(sK5(k2_zfmisc_1(X0,X1),X0),X0)) )),
% 1.39/0.59    inference(resolution,[],[f420,f85])).
% 1.39/0.59  fof(f85,plain,(
% 1.39/0.59    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK5(k2_zfmisc_1(X2,X3),X4),X4) | k1_relat_1(k2_zfmisc_1(X2,X3)) = X4 | ~r2_hidden(X5,X3) | ~r2_hidden(sK5(k2_zfmisc_1(X2,X3),X4),X2)) )),
% 1.39/0.59    inference(resolution,[],[f36,f42])).
% 1.39/0.59  fof(f42,plain,(
% 1.39/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f25])).
% 1.39/0.59  fof(f36,plain,(
% 1.39/0.59    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | k1_relat_1(X0) = X1 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f21])).
% 1.39/0.59  fof(f84,plain,(
% 1.39/0.59    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | ~r2_hidden(sK5(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.39/0.59    inference(resolution,[],[f36,f46])).
% 1.39/0.59  fof(f46,plain,(
% 1.39/0.59    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 1.39/0.59    inference(equality_resolution,[],[f33])).
% 1.39/0.59  fof(f33,plain,(
% 1.39/0.59    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.39/0.59    inference(cnf_transformation,[],[f21])).
% 1.39/0.59  fof(f1422,plain,(
% 1.39/0.59    spl8_3 | spl8_31 | ~spl8_5 | ~spl8_16),
% 1.39/0.59    inference(avatar_split_clause,[],[f1421,f998,f155,f1409,f148])).
% 1.39/0.59  fof(f1421,plain,(
% 1.39/0.59    ( ! [X24,X23,X25,X22] : (r2_hidden(k2_relat_1(k1_xboole_0),X22) | X22 = X24 | ~r2_hidden(X25,X23)) ) | (~spl8_5 | ~spl8_16)),
% 1.39/0.59    inference(subsumption_resolution,[],[f1420,f156])).
% 1.39/0.59  fof(f1420,plain,(
% 1.39/0.59    ( ! [X24,X23,X25,X22] : (r2_hidden(k2_relat_1(k1_xboole_0),X24) | r2_hidden(k2_relat_1(k1_xboole_0),X22) | X22 = X24 | ~r2_hidden(X25,X23)) ) | ~spl8_16),
% 1.39/0.59    inference(forward_demodulation,[],[f1419,f999])).
% 1.39/0.59  fof(f1419,plain,(
% 1.39/0.59    ( ! [X24,X23,X25,X22] : (r2_hidden(k2_relat_1(k1_xboole_0),X22) | r2_hidden(sK5(k2_zfmisc_1(X22,X23),X24),X24) | X22 = X24 | ~r2_hidden(X25,X23)) ) | ~spl8_16),
% 1.39/0.59    inference(forward_demodulation,[],[f1155,f999])).
% 1.39/0.59  fof(f1155,plain,(
% 1.39/0.59    ( ! [X24,X23,X25,X22] : (r2_hidden(sK5(k2_relat_1(k1_xboole_0),X24),X22) | r2_hidden(sK5(k2_zfmisc_1(X22,X23),X24),X24) | X22 = X24 | ~r2_hidden(X25,X23)) ) | ~spl8_16),
% 1.39/0.59    inference(backward_demodulation,[],[f850,f999])).
% 1.39/0.59  fof(f850,plain,(
% 1.39/0.59    ( ! [X24,X23,X25,X22] : (r2_hidden(sK5(k2_zfmisc_1(X22,X23),X24),X22) | r2_hidden(sK5(k2_zfmisc_1(X22,X23),X24),X24) | X22 = X24 | ~r2_hidden(X25,X23)) )),
% 1.39/0.59    inference(superposition,[],[f100,f804])).
% 1.39/0.59  fof(f100,plain,(
% 1.39/0.59    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3),k1_relat_1(X2)) | r2_hidden(sK5(X2,X3),X3) | k1_relat_1(X2) = X3) )),
% 1.39/0.59    inference(resolution,[],[f35,f45])).
% 1.39/0.59  fof(f45,plain,(
% 1.39/0.59    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 1.39/0.59    inference(equality_resolution,[],[f34])).
% 1.39/0.59  fof(f34,plain,(
% 1.39/0.59    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.39/0.59    inference(cnf_transformation,[],[f21])).
% 1.39/0.59  fof(f1037,plain,(
% 1.39/0.59    spl8_16 | spl8_6),
% 1.39/0.59    inference(avatar_split_clause,[],[f1036,f158,f998])).
% 1.39/0.59  fof(f158,plain,(
% 1.39/0.59    spl8_6 <=> ! [X7] : ~r2_hidden(X7,k1_xboole_0)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.39/0.59  fof(f1036,plain,(
% 1.39/0.59    ( ! [X19,X17] : (~r2_hidden(X19,k1_xboole_0) | k2_relat_1(k1_xboole_0) = X17) )),
% 1.39/0.59    inference(global_subsumption,[],[f1022])).
% 1.39/0.59  fof(f1022,plain,(
% 1.39/0.59    ( ! [X4,X5] : (k2_relat_1(k1_xboole_0) = X4 | ~r2_hidden(X5,k1_xboole_0)) )),
% 1.39/0.59    inference(global_subsumption,[],[f817])).
% 1.39/0.59  fof(f817,plain,(
% 1.39/0.59    ( ! [X2,X3] : (k2_relat_1(k1_xboole_0) = X2 | ~r2_hidden(X3,k1_xboole_0)) )),
% 1.39/0.59    inference(superposition,[],[f496,f48])).
% 1.39/0.59  fof(f48,plain,(
% 1.39/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.39/0.59    inference(equality_resolution,[],[f38])).
% 1.39/0.59  fof(f38,plain,(
% 1.39/0.59    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.39/0.59    inference(cnf_transformation,[],[f23])).
% 1.39/0.59  fof(f23,plain,(
% 1.39/0.59    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.39/0.59    inference(flattening,[],[f22])).
% 1.39/0.59  fof(f22,plain,(
% 1.39/0.59    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.39/0.59    inference(nnf_transformation,[],[f2])).
% 1.39/0.59  fof(f2,axiom,(
% 1.39/0.59    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.59  fof(f496,plain,(
% 1.39/0.59    ( ! [X2,X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | ~r2_hidden(X2,X0)) )),
% 1.39/0.59    inference(subsumption_resolution,[],[f495,f366])).
% 1.39/0.59  fof(f366,plain,(
% 1.39/0.59    ( ! [X0,X1] : (r2_hidden(sK2(k2_zfmisc_1(X0,X1),X1),X1) | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1) )),
% 1.39/0.59    inference(factoring,[],[f89])).
% 1.39/0.59  fof(f89,plain,(
% 1.39/0.59    ( ! [X6,X8,X7] : (r2_hidden(sK2(k2_zfmisc_1(X6,X7),X8),X8) | k2_relat_1(k2_zfmisc_1(X6,X7)) = X8 | r2_hidden(sK2(k2_zfmisc_1(X6,X7),X8),X7)) )),
% 1.39/0.59    inference(resolution,[],[f31,f41])).
% 1.39/0.59  fof(f495,plain,(
% 1.39/0.59    ( ! [X2,X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | ~r2_hidden(sK2(k2_zfmisc_1(X0,X1),X1),X1) | ~r2_hidden(X2,X0)) )),
% 1.39/0.59    inference(duplicate_literal_removal,[],[f480])).
% 1.39/0.59  fof(f480,plain,(
% 1.39/0.59    ( ! [X2,X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | ~r2_hidden(sK2(k2_zfmisc_1(X0,X1),X1),X1) | ~r2_hidden(X2,X0)) )),
% 1.39/0.59    inference(resolution,[],[f366,f81])).
% 1.39/0.59  fof(f81,plain,(
% 1.39/0.59    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK2(k2_zfmisc_1(X2,X3),X4),X4) | k2_relat_1(k2_zfmisc_1(X2,X3)) = X4 | ~r2_hidden(sK2(k2_zfmisc_1(X2,X3),X4),X3) | ~r2_hidden(X5,X2)) )),
% 1.39/0.59    inference(resolution,[],[f32,f42])).
% 1.39/0.59  fof(f1026,plain,(
% 1.39/0.59    spl8_6 | spl8_5),
% 1.39/0.59    inference(avatar_split_clause,[],[f179,f155,f158])).
% 1.39/0.59  fof(f179,plain,(
% 1.39/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,k1_xboole_0) | r2_hidden(X0,X3)) )),
% 1.39/0.59    inference(resolution,[],[f79,f59])).
% 1.39/0.59  fof(f59,plain,(
% 1.39/0.59    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X4,X5),k1_xboole_0) | r2_hidden(X5,X3)) )),
% 1.39/0.59    inference(superposition,[],[f41,f48])).
% 1.39/0.59  fof(f79,plain,(
% 1.39/0.59    ( ! [X4,X5,X3] : (r2_hidden(k4_tarski(X4,X5),k1_xboole_0) | ~r2_hidden(X5,X3) | ~r2_hidden(X4,k1_xboole_0)) )),
% 1.39/0.59    inference(superposition,[],[f42,f48])).
% 1.39/0.59  fof(f971,plain,(
% 1.39/0.59    spl8_2 | ~spl8_6),
% 1.39/0.59    inference(avatar_contradiction_clause,[],[f970])).
% 1.39/0.59  fof(f970,plain,(
% 1.39/0.59    $false | (spl8_2 | ~spl8_6)),
% 1.39/0.59    inference(subsumption_resolution,[],[f964,f26])).
% 1.39/0.59  fof(f26,plain,(
% 1.39/0.59    k1_xboole_0 != sK0),
% 1.39/0.59    inference(cnf_transformation,[],[f9])).
% 1.39/0.59  fof(f9,plain,(
% 1.39/0.59    (sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 1.39/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).
% 1.39/0.59  fof(f8,plain,(
% 1.39/0.59    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => ((sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 1.39/0.59    introduced(choice_axiom,[])).
% 1.39/0.59  fof(f7,plain,(
% 1.39/0.59    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.39/0.59    inference(ennf_transformation,[],[f6])).
% 1.39/0.59  fof(f6,negated_conjecture,(
% 1.39/0.59    ~! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.39/0.59    inference(negated_conjecture,[],[f5])).
% 1.39/0.59  fof(f5,conjecture,(
% 1.39/0.59    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.39/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 1.39/0.59  fof(f964,plain,(
% 1.39/0.59    k1_xboole_0 = sK0 | (spl8_2 | ~spl8_6)),
% 1.39/0.59    inference(resolution,[],[f918,f679])).
% 1.39/0.59  fof(f679,plain,(
% 1.39/0.59    ( ! [X12] : (r2_hidden(sK5(k1_xboole_0,X12),X12) | k1_xboole_0 = X12) ) | ~spl8_6),
% 1.39/0.59    inference(subsumption_resolution,[],[f631,f159])).
% 1.39/0.59  fof(f159,plain,(
% 1.39/0.59    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0)) ) | ~spl8_6),
% 1.39/0.59    inference(avatar_component_clause,[],[f158])).
% 1.39/0.59  fof(f631,plain,(
% 1.39/0.59    ( ! [X12] : (k1_xboole_0 = X12 | r2_hidden(sK5(k1_xboole_0,X12),X12) | r2_hidden(sK6(k1_xboole_0,X12),k1_xboole_0)) ) | ~spl8_6),
% 1.39/0.59    inference(backward_demodulation,[],[f104,f621])).
% 1.39/0.59  fof(f621,plain,(
% 1.39/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl8_6),
% 1.39/0.59    inference(resolution,[],[f540,f305])).
% 1.39/0.59  fof(f305,plain,(
% 1.39/0.59    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(k1_xboole_0))) ) | ~spl8_6),
% 1.39/0.59    inference(forward_demodulation,[],[f233,f47])).
% 1.39/0.59  fof(f47,plain,(
% 1.39/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.59    inference(equality_resolution,[],[f39])).
% 1.39/0.59  fof(f39,plain,(
% 1.39/0.59    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.39/0.59    inference(cnf_transformation,[],[f23])).
% 1.39/0.59  fof(f233,plain,(
% 1.39/0.59    ( ! [X4,X3] : (~r2_hidden(X3,k1_relat_1(k2_zfmisc_1(X4,k1_xboole_0)))) ) | ~spl8_6),
% 1.39/0.59    inference(resolution,[],[f69,f159])).
% 1.39/0.59  fof(f69,plain,(
% 1.39/0.59    ( ! [X6,X4,X5] : (r2_hidden(sK7(k2_zfmisc_1(X5,X6),X4),X6) | ~r2_hidden(X4,k1_relat_1(k2_zfmisc_1(X5,X6)))) )),
% 1.39/0.59    inference(resolution,[],[f46,f41])).
% 1.39/0.59  fof(f540,plain,(
% 1.39/0.59    ( ! [X12] : (r2_hidden(sK2(k1_xboole_0,X12),X12) | k1_xboole_0 = X12) ) | ~spl8_6),
% 1.39/0.59    inference(subsumption_resolution,[],[f500,f159])).
% 1.39/0.59  fof(f500,plain,(
% 1.39/0.59    ( ! [X12] : (k1_xboole_0 = X12 | r2_hidden(sK2(k1_xboole_0,X12),X12) | r2_hidden(sK2(k1_xboole_0,X12),k1_xboole_0)) ) | ~spl8_6),
% 1.39/0.59    inference(backward_demodulation,[],[f91,f497])).
% 1.39/0.59  fof(f497,plain,(
% 1.39/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl8_6),
% 1.39/0.59    inference(forward_demodulation,[],[f481,f47])).
% 1.39/0.59  fof(f481,plain,(
% 1.39/0.59    ( ! [X3] : (k1_xboole_0 = k2_relat_1(k2_zfmisc_1(X3,k1_xboole_0))) ) | ~spl8_6),
% 1.39/0.59    inference(resolution,[],[f366,f159])).
% 1.39/0.59  fof(f91,plain,(
% 1.39/0.59    ( ! [X12] : (k2_relat_1(k1_xboole_0) = X12 | r2_hidden(sK2(k1_xboole_0,X12),X12) | r2_hidden(sK2(k1_xboole_0,X12),k1_xboole_0)) )),
% 1.39/0.59    inference(resolution,[],[f31,f58])).
% 1.39/0.59  fof(f58,plain,(
% 1.39/0.59    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),k1_xboole_0) | r2_hidden(X2,k1_xboole_0)) )),
% 1.39/0.59    inference(superposition,[],[f41,f47])).
% 1.39/0.59  fof(f104,plain,(
% 1.39/0.59    ( ! [X12] : (k1_relat_1(k1_xboole_0) = X12 | r2_hidden(sK5(k1_xboole_0,X12),X12) | r2_hidden(sK6(k1_xboole_0,X12),k1_xboole_0)) )),
% 1.39/0.59    inference(resolution,[],[f35,f58])).
% 1.39/0.59  fof(f918,plain,(
% 1.39/0.59    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl8_2),
% 1.39/0.59    inference(trivial_inequality_removal,[],[f917])).
% 1.39/0.59  fof(f917,plain,(
% 1.39/0.59    ( ! [X0] : (sK1 != sK1 | ~r2_hidden(X0,sK0)) ) | spl8_2),
% 1.39/0.59    inference(superposition,[],[f54,f496])).
% 1.39/0.59  fof(f916,plain,(
% 1.39/0.59    spl8_1 | ~spl8_6),
% 1.39/0.59    inference(avatar_contradiction_clause,[],[f915])).
% 1.39/0.59  fof(f915,plain,(
% 1.39/0.59    $false | (spl8_1 | ~spl8_6)),
% 1.39/0.59    inference(subsumption_resolution,[],[f909,f27])).
% 1.39/0.59  fof(f27,plain,(
% 1.39/0.59    k1_xboole_0 != sK1),
% 1.39/0.59    inference(cnf_transformation,[],[f9])).
% 1.39/0.59  fof(f909,plain,(
% 1.39/0.59    k1_xboole_0 = sK1 | (spl8_1 | ~spl8_6)),
% 1.39/0.59    inference(resolution,[],[f854,f679])).
% 1.39/0.59  fof(f854,plain,(
% 1.39/0.59    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | spl8_1),
% 1.39/0.59    inference(trivial_inequality_removal,[],[f845])).
% 1.39/0.59  fof(f845,plain,(
% 1.39/0.59    ( ! [X0] : (sK0 != sK0 | ~r2_hidden(X0,sK1)) ) | spl8_1),
% 1.39/0.59    inference(superposition,[],[f51,f804])).
% 1.39/0.59  fof(f303,plain,(
% 1.39/0.59    spl8_1 | ~spl8_3),
% 1.39/0.59    inference(avatar_contradiction_clause,[],[f302])).
% 1.39/0.59  fof(f302,plain,(
% 1.39/0.59    $false | (spl8_1 | ~spl8_3)),
% 1.39/0.59    inference(subsumption_resolution,[],[f277,f197])).
% 1.39/0.59  fof(f197,plain,(
% 1.39/0.59    ( ! [X2,X3] : (k2_relat_1(X2) = X3) ) | ~spl8_3),
% 1.39/0.59    inference(subsumption_resolution,[],[f187,f149])).
% 1.39/0.59  fof(f149,plain,(
% 1.39/0.59    ( ! [X2,X1] : (~r2_hidden(X1,X2)) ) | ~spl8_3),
% 1.39/0.59    inference(avatar_component_clause,[],[f148])).
% 1.39/0.59  fof(f187,plain,(
% 1.39/0.59    ( ! [X2,X3] : (k2_relat_1(X2) = X3 | r2_hidden(sK2(X2,X3),X3)) ) | ~spl8_3),
% 1.39/0.59    inference(resolution,[],[f149,f31])).
% 1.39/0.59  fof(f277,plain,(
% 1.39/0.59    ( ! [X0] : (k2_relat_1(X0) != sK0) ) | (spl8_1 | ~spl8_3)),
% 1.39/0.59    inference(superposition,[],[f51,f197])).
% 1.39/0.59  fof(f55,plain,(
% 1.39/0.59    ~spl8_1 | ~spl8_2),
% 1.39/0.59    inference(avatar_split_clause,[],[f28,f53,f50])).
% 1.39/0.59  fof(f28,plain,(
% 1.39/0.59    sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.39/0.59    inference(cnf_transformation,[],[f9])).
% 1.39/0.59  % SZS output end Proof for theBenchmark
% 1.39/0.59  % (26201)------------------------------
% 1.39/0.59  % (26201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.59  % (26201)Termination reason: Refutation
% 1.39/0.59  
% 1.39/0.59  % (26201)Memory used [KB]: 11513
% 1.39/0.59  % (26201)Time elapsed: 0.154 s
% 1.39/0.59  % (26201)------------------------------
% 1.39/0.59  % (26201)------------------------------
% 1.39/0.59  % (26198)Success in time 0.233 s
%------------------------------------------------------------------------------
