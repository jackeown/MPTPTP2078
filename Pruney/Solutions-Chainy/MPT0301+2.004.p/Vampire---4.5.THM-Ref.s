%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 640 expanded)
%              Number of leaves         :   22 ( 222 expanded)
%              Depth                    :   17
%              Number of atoms          :  326 (2057 expanded)
%              Number of equality atoms :   91 ( 480 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1497,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f65,f71,f132,f571,f589,f618,f672,f696,f1071,f1496])).

fof(f1496,plain,
    ( spl8_2
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f1495])).

fof(f1495,plain,
    ( $false
    | spl8_2
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f1494,f58])).

fof(f58,plain,
    ( k1_xboole_0 != sK3
    | spl8_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1494,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f1485,f1399])).

fof(f1399,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(sK3,X0)
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f1120,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f6,f13,f12])).

fof(f12,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f1120,plain,
    ( ! [X1] : sP1(sK3,X1,k1_xboole_0)
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f430,f1086])).

fof(f1086,plain,
    ( ! [X0] : sK3 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f1073,f48])).

fof(f1073,plain,
    ( ! [X0] : sP1(k1_xboole_0,X0,sK3)
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f202,f671,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP0(sK5(X0,X1,X2),X1,X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK5(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(sK5(X0,X1,X2),X1,X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(sK5(X0,X1,X2),X1,X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X1,X0) )
            & ( sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f671,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f670])).

fof(f670,plain,
    ( spl8_13
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f202,plain,(
    ! [X0,X1] : ~ sP0(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f99,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0
          & r2_hidden(sK7(X0,X1,X2),X1)
          & r2_hidden(sK6(X0,X1,X2),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f99,plain,(
    ! [X9] : ~ r2_hidden(X9,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f91,f85])).

fof(f85,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f80,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f80,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f91,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X8) ) ),
    inference(superposition,[],[f38,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f35,f33])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f430,plain,(
    ! [X0,X1] : sP1(k2_zfmisc_1(k1_xboole_0,X0),X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f99,f277,f41])).

fof(f277,plain,(
    ! [X2,X0,X1] : ~ sP0(X0,X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(unit_resulting_resolution,[],[f274,f43])).

fof(f274,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f202,f50,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1485,plain,
    ( ! [X0] : sK3 = k2_zfmisc_1(sK3,X0)
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f1204,f48])).

fof(f1204,plain,
    ( ! [X1] : sP1(sK3,X1,sK3)
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f1123,f1086])).

fof(f1123,plain,
    ( ! [X2,X1] : sP1(sK3,X1,k2_zfmisc_1(k1_xboole_0,X2))
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f433,f1086])).

fof(f433,plain,(
    ! [X2,X0,X1] : sP1(k2_zfmisc_1(k1_xboole_0,X0),X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(unit_resulting_resolution,[],[f274,f277,f41])).

fof(f1071,plain,
    ( ~ spl8_1
    | spl8_3
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f1070])).

fof(f1070,plain,
    ( $false
    | ~ spl8_1
    | spl8_3
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f1069,f63])).

fof(f63,plain,
    ( k1_xboole_0 != sK2
    | spl8_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1069,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_1
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f1066,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1066,plain,
    ( sK2 = k2_zfmisc_1(sK2,sK3)
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f695,f48])).

fof(f695,plain,
    ( sP1(sK2,sK3,sK2)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f693])).

fof(f693,plain,
    ( spl8_14
  <=> sP1(sK2,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f696,plain,
    ( spl8_14
    | ~ spl8_1
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f687,f667,f52,f693])).

fof(f667,plain,
    ( spl8_12
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f687,plain,
    ( sP1(sK2,sK3,sK2)
    | ~ spl8_1
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f625,f668,f41])).

fof(f668,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f667])).

fof(f625,plain,
    ( ! [X2] : ~ sP0(X2,sK3,sK2)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f621,f99])).

fof(f621,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ sP0(X2,sK3,sK2) )
    | ~ spl8_1 ),
    inference(superposition,[],[f299,f53])).

fof(f299,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f40,f50])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f672,plain,
    ( spl8_12
    | spl8_13
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f662,f52,f670,f667])).

fof(f662,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl8_1 ),
    inference(resolution,[],[f625,f49])).

fof(f49,plain,(
    ! [X4,X2,X3,X1] :
      ( sP0(k4_tarski(X3,X4),X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f618,plain,(
    spl8_10 ),
    inference(avatar_contradiction_clause,[],[f617])).

fof(f617,plain,
    ( $false
    | spl8_10 ),
    inference(subsumption_resolution,[],[f615,f421])).

fof(f421,plain,(
    ! [X0] : sP1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f99,f202,f41])).

fof(f615,plain,
    ( ~ sP1(k1_xboole_0,sK3,k1_xboole_0)
    | spl8_10 ),
    inference(unit_resulting_resolution,[],[f588,f48])).

fof(f588,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl8_10
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f589,plain,
    ( ~ spl8_10
    | spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f574,f61,f52,f586])).

fof(f574,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl8_1
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f54,f62])).

% (18527)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f62,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f54,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f571,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | spl8_7 ),
    inference(subsumption_resolution,[],[f420,f238])).

fof(f238,plain,(
    ! [X0,X1] : ~ sP0(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f99,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f420,plain,
    ( sP0(sK5(sK2,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK2)
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f131,f99,f41])).

fof(f131,plain,
    ( ~ sP1(sK2,k1_xboole_0,k1_xboole_0)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_7
  <=> sP1(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f132,plain,
    ( ~ spl8_7
    | spl8_4 ),
    inference(avatar_split_clause,[],[f124,f68,f129])).

fof(f68,plain,
    ( spl8_4
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

% (18526)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f124,plain,
    ( ~ sP1(sK2,k1_xboole_0,k1_xboole_0)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f70,f48])).

fof(f70,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f71,plain,
    ( ~ spl8_4
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f66,f56,f52,f68])).

fof(f66,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0)
    | spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f54,f57])).

fof(f57,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f65,plain,
    ( spl8_1
    | spl8_3
    | spl8_2 ),
    inference(avatar_split_clause,[],[f30,f56,f61,f52])).

fof(f30,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2 )
      | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2 )
        | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

% (18522)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f15,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f64,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f31,f61,f52])).

fof(f31,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f32,f56,f52])).

fof(f32,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:18:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (18523)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (18524)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (18508)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (18515)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (18508)Refutation not found, incomplete strategy% (18508)------------------------------
% 0.22/0.48  % (18508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (18508)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (18508)Memory used [KB]: 6140
% 0.22/0.48  % (18508)Time elapsed: 0.058 s
% 0.22/0.48  % (18508)------------------------------
% 0.22/0.48  % (18508)------------------------------
% 0.22/0.50  % (18514)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (18520)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (18520)Refutation not found, incomplete strategy% (18520)------------------------------
% 0.22/0.50  % (18520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18520)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (18520)Memory used [KB]: 6012
% 0.22/0.50  % (18520)Time elapsed: 0.001 s
% 0.22/0.50  % (18520)------------------------------
% 0.22/0.50  % (18520)------------------------------
% 0.22/0.50  % (18510)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (18511)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (18511)Refutation not found, incomplete strategy% (18511)------------------------------
% 0.22/0.50  % (18511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18511)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (18511)Memory used [KB]: 10618
% 0.22/0.50  % (18511)Time elapsed: 0.081 s
% 0.22/0.50  % (18511)------------------------------
% 0.22/0.50  % (18511)------------------------------
% 0.22/0.50  % (18521)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (18524)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f1497,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f59,f64,f65,f71,f132,f571,f589,f618,f672,f696,f1071,f1496])).
% 0.22/0.51  fof(f1496,plain,(
% 0.22/0.51    spl8_2 | ~spl8_13),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f1495])).
% 0.22/0.51  fof(f1495,plain,(
% 0.22/0.51    $false | (spl8_2 | ~spl8_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f1494,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    k1_xboole_0 != sK3 | spl8_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    spl8_2 <=> k1_xboole_0 = sK3),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.51  fof(f1494,plain,(
% 0.22/0.51    k1_xboole_0 = sK3 | ~spl8_13),
% 0.22/0.51    inference(forward_demodulation,[],[f1485,f1399])).
% 0.22/0.51  fof(f1399,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(sK3,X0)) ) | ~spl8_13),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f1120,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.22/0.51    inference(definition_folding,[],[f6,f13,f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X1,X0)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.51  fof(f1120,plain,(
% 0.22/0.51    ( ! [X1] : (sP1(sK3,X1,k1_xboole_0)) ) | ~spl8_13),
% 0.22/0.51    inference(backward_demodulation,[],[f430,f1086])).
% 0.22/0.51  fof(f1086,plain,(
% 0.22/0.51    ( ! [X0] : (sK3 = k2_zfmisc_1(k1_xboole_0,X0)) ) | ~spl8_13),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f1073,f48])).
% 0.22/0.51  fof(f1073,plain,(
% 0.22/0.51    ( ! [X0] : (sP1(k1_xboole_0,X0,sK3)) ) | ~spl8_13),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f202,f671,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (sP0(sK5(X0,X1,X2),X1,X0) | sP1(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.51    inference(rectify,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X1,X0)) & (sP0(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.51    inference(nnf_transformation,[],[f13])).
% 0.22/0.51  fof(f671,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl8_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f670])).
% 0.22/0.51  fof(f670,plain,(
% 0.22/0.51    spl8_13 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP0(X0,X1,k1_xboole_0)) )),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f99,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0 & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X2)) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f26,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0 & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X2)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(rectify,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP0(X3,X1,X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f12])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X9] : (~r2_hidden(X9,k1_xboole_0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f91,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f80,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.51    inference(superposition,[],[f36,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ( ! [X8,X9] : (~r2_hidden(X9,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X8)) )),
% 0.22/0.51    inference(superposition,[],[f38,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(superposition,[],[f35,f33])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.51  fof(f430,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP1(k2_zfmisc_1(k1_xboole_0,X0),X1,k1_xboole_0)) )),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f99,f277,f41])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,k2_zfmisc_1(k1_xboole_0,X2))) )),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f274,f43])).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f202,f50,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X4,X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f1485,plain,(
% 0.22/0.51    ( ! [X0] : (sK3 = k2_zfmisc_1(sK3,X0)) ) | ~spl8_13),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f1204,f48])).
% 0.22/0.51  fof(f1204,plain,(
% 0.22/0.51    ( ! [X1] : (sP1(sK3,X1,sK3)) ) | ~spl8_13),
% 0.22/0.51    inference(forward_demodulation,[],[f1123,f1086])).
% 0.22/0.51  fof(f1123,plain,(
% 0.22/0.51    ( ! [X2,X1] : (sP1(sK3,X1,k2_zfmisc_1(k1_xboole_0,X2))) ) | ~spl8_13),
% 0.22/0.51    inference(backward_demodulation,[],[f433,f1086])).
% 0.22/0.51  fof(f433,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (sP1(k2_zfmisc_1(k1_xboole_0,X0),X1,k2_zfmisc_1(k1_xboole_0,X2))) )),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f274,f277,f41])).
% 0.22/0.51  fof(f1071,plain,(
% 0.22/0.51    ~spl8_1 | spl8_3 | ~spl8_14),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f1070])).
% 0.22/0.51  fof(f1070,plain,(
% 0.22/0.51    $false | (~spl8_1 | spl8_3 | ~spl8_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f1069,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    k1_xboole_0 != sK2 | spl8_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    spl8_3 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.51  fof(f1069,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | (~spl8_1 | ~spl8_14)),
% 0.22/0.51    inference(forward_demodulation,[],[f1066,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    k1_xboole_0 = k2_zfmisc_1(sK2,sK3) | ~spl8_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.51  fof(f1066,plain,(
% 0.22/0.51    sK2 = k2_zfmisc_1(sK2,sK3) | ~spl8_14),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f695,f48])).
% 0.22/0.51  fof(f695,plain,(
% 0.22/0.51    sP1(sK2,sK3,sK2) | ~spl8_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f693])).
% 0.22/0.51  fof(f693,plain,(
% 0.22/0.51    spl8_14 <=> sP1(sK2,sK3,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.51  fof(f696,plain,(
% 0.22/0.51    spl8_14 | ~spl8_1 | ~spl8_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f687,f667,f52,f693])).
% 0.22/0.51  fof(f667,plain,(
% 0.22/0.51    spl8_12 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.51  fof(f687,plain,(
% 0.22/0.51    sP1(sK2,sK3,sK2) | (~spl8_1 | ~spl8_12)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f625,f668,f41])).
% 0.22/0.51  fof(f668,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl8_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f667])).
% 0.22/0.51  fof(f625,plain,(
% 0.22/0.51    ( ! [X2] : (~sP0(X2,sK3,sK2)) ) | ~spl8_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f621,f99])).
% 0.22/0.51  fof(f621,plain,(
% 0.22/0.51    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~sP0(X2,sK3,sK2)) ) | ~spl8_1),
% 0.22/0.51    inference(superposition,[],[f299,f53])).
% 0.22/0.51  fof(f299,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_zfmisc_1(X2,X1)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(resolution,[],[f40,f50])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f672,plain,(
% 0.22/0.51    spl8_12 | spl8_13 | ~spl8_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f662,f52,f670,f667])).
% 0.22/0.51  fof(f662,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK2)) ) | ~spl8_1),
% 0.22/0.51    inference(resolution,[],[f625,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (sP0(k4_tarski(X3,X4),X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2) | k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f618,plain,(
% 0.22/0.51    spl8_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f617])).
% 0.22/0.51  fof(f617,plain,(
% 0.22/0.51    $false | spl8_10),
% 0.22/0.51    inference(subsumption_resolution,[],[f615,f421])).
% 0.22/0.51  fof(f421,plain,(
% 0.22/0.51    ( ! [X0] : (sP1(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f99,f202,f41])).
% 0.22/0.51  fof(f615,plain,(
% 0.22/0.51    ~sP1(k1_xboole_0,sK3,k1_xboole_0) | spl8_10),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f588,f48])).
% 0.22/0.51  fof(f588,plain,(
% 0.22/0.51    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | spl8_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f586])).
% 0.22/0.51  fof(f586,plain,(
% 0.22/0.51    spl8_10 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.51  fof(f589,plain,(
% 0.22/0.51    ~spl8_10 | spl8_1 | ~spl8_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f574,f61,f52,f586])).
% 0.22/0.51  fof(f574,plain,(
% 0.22/0.51    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (spl8_1 | ~spl8_3)),
% 0.22/0.51    inference(backward_demodulation,[],[f54,f62])).
% 0.22/0.51  % (18527)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl8_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f61])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    k1_xboole_0 != k2_zfmisc_1(sK2,sK3) | spl8_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f52])).
% 0.22/0.51  fof(f571,plain,(
% 0.22/0.51    spl8_7),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f570])).
% 0.22/0.51  fof(f570,plain,(
% 0.22/0.51    $false | spl8_7),
% 0.22/0.51    inference(subsumption_resolution,[],[f420,f238])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP0(X0,k1_xboole_0,X1)) )),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f99,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | ~sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f420,plain,(
% 0.22/0.51    sP0(sK5(sK2,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK2) | spl8_7),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f131,f99,f41])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ~sP1(sK2,k1_xboole_0,k1_xboole_0) | spl8_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f129])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl8_7 <=> sP1(sK2,k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ~spl8_7 | spl8_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f124,f68,f129])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl8_4 <=> k1_xboole_0 = k2_zfmisc_1(sK2,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.51  % (18526)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ~sP1(sK2,k1_xboole_0,k1_xboole_0) | spl8_4),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f70,f48])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0) | spl8_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f68])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ~spl8_4 | spl8_1 | ~spl8_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f66,f56,f52,f68])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0) | (spl8_1 | ~spl8_2)),
% 0.22/0.51    inference(forward_demodulation,[],[f54,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    k1_xboole_0 = sK3 | ~spl8_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f56])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl8_1 | spl8_3 | spl8_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f30,f56,f61,f52])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ((k1_xboole_0 != sK3 & k1_xboole_0 != sK2) | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)) & (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK3 & k1_xboole_0 != sK2) | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)) & (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  % (18522)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    inference(negated_conjecture,[],[f7])).
% 0.22/0.51  fof(f7,conjecture,(
% 0.22/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ~spl8_1 | ~spl8_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f31,f61,f52])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ~spl8_1 | ~spl8_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f32,f56,f52])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    k1_xboole_0 != sK3 | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (18524)------------------------------
% 0.22/0.51  % (18524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18524)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (18524)Memory used [KB]: 11257
% 0.22/0.51  % (18524)Time elapsed: 0.084 s
% 0.22/0.51  % (18524)------------------------------
% 0.22/0.51  % (18524)------------------------------
% 0.22/0.51  % (18513)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (18507)Success in time 0.148 s
%------------------------------------------------------------------------------
