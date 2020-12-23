%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:35 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 261 expanded)
%              Number of leaves         :   25 ( 105 expanded)
%              Depth                    :    9
%              Number of atoms          :  352 ( 700 expanded)
%              Number of equality atoms :   75 ( 186 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1335,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f67,f72,f87,f154,f181,f321,f429,f452,f459,f526,f589,f773,f1030,f1111,f1125,f1128,f1330])).

fof(f1330,plain,
    ( spl8_1
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f1289,f165,f64,f50])).

fof(f50,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f64,plain,
    ( spl8_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f165,plain,
    ( spl8_14
  <=> ! [X5] : ~ r2_hidden(X5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f1289,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(superposition,[],[f1288,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1288,plain,
    ( ! [X0] : sK0 = k4_xboole_0(X0,X0)
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(duplicate_literal_removal,[],[f1278])).

fof(f1278,plain,
    ( ! [X0] :
        ( sK0 = k4_xboole_0(X0,X0)
        | sK0 = k4_xboole_0(X0,X0) )
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(resolution,[],[f1138,f1137])).

fof(f1137,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK7(X5,X6,sK0),X5)
        | sK0 = k4_xboole_0(X5,X6) )
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(resolution,[],[f1130,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | r2_hidden(sK7(X0,X1,X2),X0)
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

fof(f1130,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK0)
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f166,f65])).

fof(f65,plain,
    ( sK0 = sK2
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f166,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK2)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f1138,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(sK7(X7,X8,sK0),X8)
        | sK0 = k4_xboole_0(X7,X8) )
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(resolution,[],[f1130,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1128,plain,
    ( spl8_3
    | ~ spl8_37
    | spl8_38 ),
    inference(avatar_contradiction_clause,[],[f1126])).

fof(f1126,plain,
    ( $false
    | spl8_3
    | ~ spl8_37
    | spl8_38 ),
    inference(unit_resulting_resolution,[],[f1110,f62,f1124,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f1124,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | spl8_38 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f1122,plain,
    ( spl8_38
  <=> r2_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f62,plain,
    ( sK1 != sK3
    | spl8_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1110,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f1108])).

fof(f1108,plain,
    ( spl8_37
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f1125,plain,
    ( ~ spl8_38
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f1120,f524,f1122])).

fof(f524,plain,
    ( spl8_26
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f1120,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | ~ spl8_26 ),
    inference(duplicate_literal_removal,[],[f1117])).

fof(f1117,plain,
    ( ~ r2_xboole_0(sK3,sK1)
    | ~ r2_xboole_0(sK3,sK1)
    | ~ spl8_26 ),
    inference(resolution,[],[f1054,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f1054,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK3,X0),sK1)
        | ~ r2_xboole_0(sK3,X0) )
    | ~ spl8_26 ),
    inference(resolution,[],[f525,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f525,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f524])).

fof(f1111,plain,
    ( spl8_37
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f1106,f179,f1108])).

fof(f179,plain,
    ( spl8_16
  <=> ! [X6] :
        ( ~ r2_hidden(X6,sK3)
        | r2_hidden(X6,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f1106,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl8_16 ),
    inference(duplicate_literal_removal,[],[f1103])).

fof(f1103,plain,
    ( r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1)
    | ~ spl8_16 ),
    inference(resolution,[],[f262,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f262,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK5(X3,sK1),sK3)
        | r1_tarski(X3,sK1) )
    | ~ spl8_16 ),
    inference(resolution,[],[f180,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f180,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK1)
        | ~ r2_hidden(X6,sK3) )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f1030,plain,
    ( spl8_1
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f983,f521,f50])).

fof(f521,plain,
    ( spl8_25
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f983,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_25 ),
    inference(superposition,[],[f982,f20])).

fof(f982,plain,
    ( ! [X0] : sK0 = k4_xboole_0(X0,X0)
    | ~ spl8_25 ),
    inference(duplicate_literal_removal,[],[f972])).

fof(f972,plain,
    ( ! [X0] :
        ( sK0 = k4_xboole_0(X0,X0)
        | sK0 = k4_xboole_0(X0,X0) )
    | ~ spl8_25 ),
    inference(resolution,[],[f788,f787])).

fof(f787,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK7(X5,X6,sK0),X5)
        | sK0 = k4_xboole_0(X5,X6) )
    | ~ spl8_25 ),
    inference(resolution,[],[f522,f35])).

fof(f522,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f521])).

fof(f788,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(sK7(X7,X8,sK0),X8)
        | sK0 = k4_xboole_0(X7,X8) )
    | ~ spl8_25 ),
    inference(resolution,[],[f522,f36])).

fof(f773,plain,
    ( spl8_2
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f740,f152,f60,f55])).

fof(f55,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f152,plain,
    ( spl8_12
  <=> ! [X4] : ~ r2_hidden(X4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f740,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(superposition,[],[f739,f20])).

fof(f739,plain,
    ( ! [X0] : sK1 = k4_xboole_0(X0,X0)
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(duplicate_literal_removal,[],[f729])).

fof(f729,plain,
    ( ! [X0] :
        ( sK1 = k4_xboole_0(X0,X0)
        | sK1 = k4_xboole_0(X0,X0) )
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(resolution,[],[f690,f687])).

fof(f687,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK7(X5,X6,sK1),X5)
        | sK1 = k4_xboole_0(X5,X6) )
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f686,f61])).

fof(f61,plain,
    ( sK1 = sK3
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f686,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK7(X5,X6,sK1),X5)
        | sK3 = k4_xboole_0(X5,X6) )
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f471,f61])).

fof(f471,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK7(X5,X6,sK3),X5)
        | sK3 = k4_xboole_0(X5,X6) )
    | ~ spl8_12 ),
    inference(resolution,[],[f153,f35])).

fof(f153,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f690,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(sK7(X7,X8,sK1),X8)
        | sK1 = k4_xboole_0(X7,X8) )
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f689,f61])).

fof(f689,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(sK7(X7,X8,sK1),X8)
        | sK3 = k4_xboole_0(X7,X8) )
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f472,f61])).

fof(f472,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(sK7(X7,X8,sK3),X8)
        | sK3 = k4_xboole_0(X7,X8) )
    | ~ spl8_12 ),
    inference(resolution,[],[f153,f36])).

fof(f589,plain,
    ( spl8_3
    | ~ spl8_12
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f559,f524,f152,f60])).

fof(f559,plain,
    ( sK1 = sK3
    | ~ spl8_12
    | ~ spl8_26 ),
    inference(resolution,[],[f548,f468])).

fof(f468,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(X2,sK3),X2)
        | sK3 = X2 )
    | ~ spl8_12 ),
    inference(resolution,[],[f153,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f548,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl8_12
    | ~ spl8_26 ),
    inference(resolution,[],[f525,f153])).

fof(f526,plain,
    ( spl8_25
    | spl8_26
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f79,f69,f524,f521])).

fof(f69,plain,
    ( spl8_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f74,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f74,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK3) )
    | ~ spl8_5 ),
    inference(superposition,[],[f41,f71])).

fof(f71,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f459,plain,
    ( ~ spl8_20
    | spl8_4
    | spl8_21 ),
    inference(avatar_split_clause,[],[f454,f449,f64,f318])).

fof(f318,plain,
    ( spl8_20
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f449,plain,
    ( spl8_21
  <=> r2_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f454,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK2,sK0)
    | spl8_21 ),
    inference(resolution,[],[f451,f28])).

fof(f451,plain,
    ( ~ r2_xboole_0(sK2,sK0)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f449])).

fof(f452,plain,
    ( ~ spl8_21
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f447,f85,f449])).

fof(f85,plain,
    ( spl8_7
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f447,plain,
    ( ~ r2_xboole_0(sK2,sK0)
    | ~ spl8_7 ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,
    ( ~ r2_xboole_0(sK2,sK0)
    | ~ r2_xboole_0(sK2,sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f435,f32])).

fof(f435,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK6(sK2,X2),sK0)
        | ~ r2_xboole_0(sK2,X2) )
    | ~ spl8_7 ),
    inference(resolution,[],[f86,f33])).

fof(f86,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f429,plain,
    ( spl8_2
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f397,f82,f55])).

fof(f82,plain,
    ( spl8_6
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f397,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_6 ),
    inference(superposition,[],[f396,f20])).

fof(f396,plain,
    ( ! [X0] : sK1 = k4_xboole_0(X0,X0)
    | ~ spl8_6 ),
    inference(duplicate_literal_removal,[],[f386])).

fof(f386,plain,
    ( ! [X0] :
        ( sK1 = k4_xboole_0(X0,X0)
        | sK1 = k4_xboole_0(X0,X0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f253,f252])).

fof(f252,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK7(X5,X6,sK1),X5)
        | sK1 = k4_xboole_0(X5,X6) )
    | ~ spl8_6 ),
    inference(resolution,[],[f83,f35])).

fof(f83,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f253,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(sK7(X7,X8,sK1),X8)
        | sK1 = k4_xboole_0(X7,X8) )
    | ~ spl8_6 ),
    inference(resolution,[],[f83,f36])).

fof(f321,plain,
    ( spl8_20
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f316,f149,f318])).

fof(f149,plain,
    ( spl8_11
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f316,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,
    ( r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0)
    | ~ spl8_11 ),
    inference(resolution,[],[f157,f24])).

fof(f157,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(X2,sK0),sK2)
        | r1_tarski(X2,sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f150,f25])).

fof(f150,plain,
    ( ! [X5] :
        ( r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f181,plain,
    ( spl8_14
    | spl8_16
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f145,f69,f179,f165])).

fof(f145,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X7,sK2)
        | r2_hidden(X6,sK1) )
    | ~ spl8_5 ),
    inference(resolution,[],[f75,f41])).

fof(f75,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X4,sK2) )
    | ~ spl8_5 ),
    inference(superposition,[],[f42,f71])).

fof(f154,plain,
    ( spl8_11
    | spl8_12
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f144,f69,f152,f149])).

fof(f144,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK3)
        | ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,
    ( spl8_6
    | spl8_7
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f77,f69,f85,f82])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f73,f42])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK2) )
    | ~ spl8_5 ),
    inference(superposition,[],[f40,f71])).

fof(f72,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f17,f69])).

fof(f17,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f67,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f16,f64,f60])).

fof(f16,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f19,f55])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f18,f50])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:39:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (11013)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (11028)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (11012)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (11021)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (11020)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.57  % (11029)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.69/0.58  % (11008)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.69/0.60  % (11018)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.69/0.60  % (11024)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.69/0.60  % (11025)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.69/0.60  % (11009)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.69/0.60  % (11010)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.69/0.61  % (11027)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.69/0.61  % (11011)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.69/0.61  % (11023)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.69/0.61  % (11031)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.69/0.61  % (11032)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.69/0.61  % (11017)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.69/0.61  % (11026)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.69/0.61  % (11015)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.69/0.62  % (11035)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.69/0.62  % (11026)Refutation not found, incomplete strategy% (11026)------------------------------
% 1.69/0.62  % (11026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (11026)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.62  
% 1.69/0.62  % (11026)Memory used [KB]: 10746
% 1.69/0.62  % (11026)Time elapsed: 0.191 s
% 1.69/0.62  % (11026)------------------------------
% 1.69/0.62  % (11026)------------------------------
% 1.69/0.62  % (11023)Refutation not found, incomplete strategy% (11023)------------------------------
% 1.69/0.62  % (11023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (11023)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.62  
% 1.69/0.62  % (11023)Memory used [KB]: 10618
% 1.69/0.62  % (11023)Time elapsed: 0.136 s
% 1.69/0.62  % (11023)------------------------------
% 1.69/0.62  % (11023)------------------------------
% 1.69/0.62  % (11033)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.69/0.62  % (11034)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.69/0.62  % (11019)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.69/0.62  % (11007)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.69/0.62  % (11016)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.69/0.62  % (11022)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.69/0.63  % (11006)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.69/0.63  % (11006)Refutation not found, incomplete strategy% (11006)------------------------------
% 1.69/0.63  % (11006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.63  % (11006)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.63  
% 1.69/0.63  % (11006)Memory used [KB]: 1663
% 1.69/0.63  % (11006)Time elapsed: 0.197 s
% 1.69/0.63  % (11006)------------------------------
% 1.69/0.63  % (11006)------------------------------
% 1.69/0.63  % (11027)Refutation not found, incomplete strategy% (11027)------------------------------
% 1.69/0.63  % (11027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.63  % (11030)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.69/0.63  % (11008)Refutation not found, incomplete strategy% (11008)------------------------------
% 1.69/0.63  % (11008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.63  % (11008)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.63  
% 1.69/0.63  % (11008)Memory used [KB]: 10874
% 1.69/0.63  % (11008)Time elapsed: 0.210 s
% 1.69/0.63  % (11008)------------------------------
% 1.69/0.63  % (11008)------------------------------
% 1.69/0.63  % (11014)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.69/0.63  % (11027)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.63  
% 1.69/0.63  % (11027)Memory used [KB]: 1663
% 1.69/0.63  % (11027)Time elapsed: 0.201 s
% 1.69/0.63  % (11027)------------------------------
% 1.69/0.63  % (11027)------------------------------
% 1.69/0.65  % (11028)Refutation found. Thanks to Tanya!
% 1.69/0.65  % SZS status Theorem for theBenchmark
% 1.69/0.66  % SZS output start Proof for theBenchmark
% 1.69/0.66  fof(f1335,plain,(
% 1.69/0.66    $false),
% 1.69/0.66    inference(avatar_sat_refutation,[],[f53,f58,f67,f72,f87,f154,f181,f321,f429,f452,f459,f526,f589,f773,f1030,f1111,f1125,f1128,f1330])).
% 1.69/0.66  fof(f1330,plain,(
% 1.69/0.66    spl8_1 | ~spl8_4 | ~spl8_14),
% 1.69/0.66    inference(avatar_split_clause,[],[f1289,f165,f64,f50])).
% 1.69/0.66  fof(f50,plain,(
% 1.69/0.66    spl8_1 <=> k1_xboole_0 = sK0),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.69/0.66  fof(f64,plain,(
% 1.69/0.66    spl8_4 <=> sK0 = sK2),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.69/0.66  fof(f165,plain,(
% 1.69/0.66    spl8_14 <=> ! [X5] : ~r2_hidden(X5,sK2)),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.69/0.66  fof(f1289,plain,(
% 1.69/0.66    k1_xboole_0 = sK0 | (~spl8_4 | ~spl8_14)),
% 1.69/0.66    inference(superposition,[],[f1288,f20])).
% 1.69/0.66  fof(f20,plain,(
% 1.69/0.66    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.69/0.66    inference(cnf_transformation,[],[f6])).
% 1.69/0.66  fof(f6,axiom,(
% 1.69/0.66    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.69/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.69/0.66  fof(f1288,plain,(
% 1.69/0.66    ( ! [X0] : (sK0 = k4_xboole_0(X0,X0)) ) | (~spl8_4 | ~spl8_14)),
% 1.69/0.66    inference(duplicate_literal_removal,[],[f1278])).
% 1.69/0.66  fof(f1278,plain,(
% 1.69/0.66    ( ! [X0] : (sK0 = k4_xboole_0(X0,X0) | sK0 = k4_xboole_0(X0,X0)) ) | (~spl8_4 | ~spl8_14)),
% 1.69/0.66    inference(resolution,[],[f1138,f1137])).
% 1.69/0.66  fof(f1137,plain,(
% 1.69/0.66    ( ! [X6,X5] : (r2_hidden(sK7(X5,X6,sK0),X5) | sK0 = k4_xboole_0(X5,X6)) ) | (~spl8_4 | ~spl8_14)),
% 1.69/0.66    inference(resolution,[],[f1130,f35])).
% 1.69/0.66  fof(f35,plain,(
% 1.69/0.66    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | r2_hidden(sK7(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.69/0.66    inference(cnf_transformation,[],[f2])).
% 1.69/0.66  fof(f2,axiom,(
% 1.69/0.66    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.69/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.69/0.66  fof(f1130,plain,(
% 1.69/0.66    ( ! [X5] : (~r2_hidden(X5,sK0)) ) | (~spl8_4 | ~spl8_14)),
% 1.69/0.66    inference(forward_demodulation,[],[f166,f65])).
% 1.69/0.66  fof(f65,plain,(
% 1.69/0.66    sK0 = sK2 | ~spl8_4),
% 1.69/0.66    inference(avatar_component_clause,[],[f64])).
% 1.69/0.66  fof(f166,plain,(
% 1.69/0.66    ( ! [X5] : (~r2_hidden(X5,sK2)) ) | ~spl8_14),
% 1.69/0.66    inference(avatar_component_clause,[],[f165])).
% 1.69/0.66  fof(f1138,plain,(
% 1.69/0.66    ( ! [X8,X7] : (~r2_hidden(sK7(X7,X8,sK0),X8) | sK0 = k4_xboole_0(X7,X8)) ) | (~spl8_4 | ~spl8_14)),
% 1.69/0.66    inference(resolution,[],[f1130,f36])).
% 1.69/0.66  fof(f36,plain,(
% 1.69/0.66    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | ~r2_hidden(sK7(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2) )),
% 1.69/0.66    inference(cnf_transformation,[],[f2])).
% 1.69/0.66  fof(f1128,plain,(
% 1.69/0.66    spl8_3 | ~spl8_37 | spl8_38),
% 1.69/0.66    inference(avatar_contradiction_clause,[],[f1126])).
% 1.69/0.66  fof(f1126,plain,(
% 1.69/0.66    $false | (spl8_3 | ~spl8_37 | spl8_38)),
% 1.69/0.66    inference(unit_resulting_resolution,[],[f1110,f62,f1124,f28])).
% 1.69/0.66  fof(f28,plain,(
% 1.69/0.66    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.69/0.66    inference(cnf_transformation,[],[f3])).
% 1.69/0.66  fof(f3,axiom,(
% 1.69/0.66    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.69/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.69/0.66  fof(f1124,plain,(
% 1.69/0.66    ~r2_xboole_0(sK3,sK1) | spl8_38),
% 1.69/0.66    inference(avatar_component_clause,[],[f1122])).
% 1.69/0.66  fof(f1122,plain,(
% 1.69/0.66    spl8_38 <=> r2_xboole_0(sK3,sK1)),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 1.69/0.66  fof(f62,plain,(
% 1.69/0.66    sK1 != sK3 | spl8_3),
% 1.69/0.66    inference(avatar_component_clause,[],[f60])).
% 1.69/0.66  fof(f60,plain,(
% 1.69/0.66    spl8_3 <=> sK1 = sK3),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.69/0.66  fof(f1110,plain,(
% 1.69/0.66    r1_tarski(sK3,sK1) | ~spl8_37),
% 1.69/0.66    inference(avatar_component_clause,[],[f1108])).
% 1.69/0.66  fof(f1108,plain,(
% 1.69/0.66    spl8_37 <=> r1_tarski(sK3,sK1)),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 1.69/0.66  fof(f1125,plain,(
% 1.69/0.66    ~spl8_38 | ~spl8_26),
% 1.69/0.66    inference(avatar_split_clause,[],[f1120,f524,f1122])).
% 1.69/0.66  fof(f524,plain,(
% 1.69/0.66    spl8_26 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.69/0.66  fof(f1120,plain,(
% 1.69/0.66    ~r2_xboole_0(sK3,sK1) | ~spl8_26),
% 1.69/0.66    inference(duplicate_literal_removal,[],[f1117])).
% 1.69/0.66  fof(f1117,plain,(
% 1.69/0.66    ~r2_xboole_0(sK3,sK1) | ~r2_xboole_0(sK3,sK1) | ~spl8_26),
% 1.69/0.66    inference(resolution,[],[f1054,f32])).
% 1.69/0.66  fof(f32,plain,(
% 1.69/0.66    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 1.69/0.66    inference(cnf_transformation,[],[f15])).
% 1.69/0.66  fof(f15,plain,(
% 1.69/0.66    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.69/0.66    inference(ennf_transformation,[],[f5])).
% 1.69/0.66  fof(f5,axiom,(
% 1.69/0.66    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.69/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.69/0.66  fof(f1054,plain,(
% 1.69/0.66    ( ! [X0] : (~r2_hidden(sK6(sK3,X0),sK1) | ~r2_xboole_0(sK3,X0)) ) | ~spl8_26),
% 1.69/0.66    inference(resolution,[],[f525,f33])).
% 1.69/0.66  fof(f33,plain,(
% 1.69/0.66    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.69/0.66    inference(cnf_transformation,[],[f15])).
% 1.69/0.66  fof(f525,plain,(
% 1.69/0.66    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl8_26),
% 1.69/0.66    inference(avatar_component_clause,[],[f524])).
% 1.69/0.66  fof(f1111,plain,(
% 1.69/0.66    spl8_37 | ~spl8_16),
% 1.69/0.66    inference(avatar_split_clause,[],[f1106,f179,f1108])).
% 1.69/0.66  fof(f179,plain,(
% 1.69/0.66    spl8_16 <=> ! [X6] : (~r2_hidden(X6,sK3) | r2_hidden(X6,sK1))),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.69/0.66  fof(f1106,plain,(
% 1.69/0.66    r1_tarski(sK3,sK1) | ~spl8_16),
% 1.69/0.66    inference(duplicate_literal_removal,[],[f1103])).
% 1.69/0.66  fof(f1103,plain,(
% 1.69/0.66    r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1) | ~spl8_16),
% 1.69/0.66    inference(resolution,[],[f262,f24])).
% 1.69/0.66  fof(f24,plain,(
% 1.69/0.66    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.69/0.66    inference(cnf_transformation,[],[f14])).
% 1.69/0.66  fof(f14,plain,(
% 1.69/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.69/0.66    inference(ennf_transformation,[],[f1])).
% 1.69/0.66  fof(f1,axiom,(
% 1.69/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.69/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.69/0.66  fof(f262,plain,(
% 1.69/0.66    ( ! [X3] : (~r2_hidden(sK5(X3,sK1),sK3) | r1_tarski(X3,sK1)) ) | ~spl8_16),
% 1.69/0.66    inference(resolution,[],[f180,f25])).
% 1.69/0.66  fof(f25,plain,(
% 1.69/0.66    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.69/0.66    inference(cnf_transformation,[],[f14])).
% 1.69/0.66  fof(f180,plain,(
% 1.69/0.66    ( ! [X6] : (r2_hidden(X6,sK1) | ~r2_hidden(X6,sK3)) ) | ~spl8_16),
% 1.69/0.66    inference(avatar_component_clause,[],[f179])).
% 1.69/0.66  fof(f1030,plain,(
% 1.69/0.66    spl8_1 | ~spl8_25),
% 1.69/0.66    inference(avatar_split_clause,[],[f983,f521,f50])).
% 1.69/0.66  fof(f521,plain,(
% 1.69/0.66    spl8_25 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.69/0.66  fof(f983,plain,(
% 1.69/0.66    k1_xboole_0 = sK0 | ~spl8_25),
% 1.69/0.66    inference(superposition,[],[f982,f20])).
% 1.69/0.66  fof(f982,plain,(
% 1.69/0.66    ( ! [X0] : (sK0 = k4_xboole_0(X0,X0)) ) | ~spl8_25),
% 1.69/0.66    inference(duplicate_literal_removal,[],[f972])).
% 1.69/0.66  fof(f972,plain,(
% 1.69/0.66    ( ! [X0] : (sK0 = k4_xboole_0(X0,X0) | sK0 = k4_xboole_0(X0,X0)) ) | ~spl8_25),
% 1.69/0.66    inference(resolution,[],[f788,f787])).
% 1.69/0.66  fof(f787,plain,(
% 1.69/0.66    ( ! [X6,X5] : (r2_hidden(sK7(X5,X6,sK0),X5) | sK0 = k4_xboole_0(X5,X6)) ) | ~spl8_25),
% 1.69/0.66    inference(resolution,[],[f522,f35])).
% 1.69/0.66  fof(f522,plain,(
% 1.69/0.66    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl8_25),
% 1.69/0.66    inference(avatar_component_clause,[],[f521])).
% 1.69/0.66  fof(f788,plain,(
% 1.69/0.66    ( ! [X8,X7] : (~r2_hidden(sK7(X7,X8,sK0),X8) | sK0 = k4_xboole_0(X7,X8)) ) | ~spl8_25),
% 1.69/0.66    inference(resolution,[],[f522,f36])).
% 1.69/0.66  fof(f773,plain,(
% 1.69/0.66    spl8_2 | ~spl8_3 | ~spl8_12),
% 1.69/0.66    inference(avatar_split_clause,[],[f740,f152,f60,f55])).
% 1.69/0.66  fof(f55,plain,(
% 1.69/0.66    spl8_2 <=> k1_xboole_0 = sK1),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.69/0.66  fof(f152,plain,(
% 1.69/0.66    spl8_12 <=> ! [X4] : ~r2_hidden(X4,sK3)),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.69/0.66  fof(f740,plain,(
% 1.69/0.66    k1_xboole_0 = sK1 | (~spl8_3 | ~spl8_12)),
% 1.69/0.66    inference(superposition,[],[f739,f20])).
% 1.69/0.66  fof(f739,plain,(
% 1.69/0.66    ( ! [X0] : (sK1 = k4_xboole_0(X0,X0)) ) | (~spl8_3 | ~spl8_12)),
% 1.69/0.66    inference(duplicate_literal_removal,[],[f729])).
% 1.69/0.66  fof(f729,plain,(
% 1.69/0.66    ( ! [X0] : (sK1 = k4_xboole_0(X0,X0) | sK1 = k4_xboole_0(X0,X0)) ) | (~spl8_3 | ~spl8_12)),
% 1.69/0.66    inference(resolution,[],[f690,f687])).
% 1.69/0.66  fof(f687,plain,(
% 1.69/0.66    ( ! [X6,X5] : (r2_hidden(sK7(X5,X6,sK1),X5) | sK1 = k4_xboole_0(X5,X6)) ) | (~spl8_3 | ~spl8_12)),
% 1.69/0.66    inference(forward_demodulation,[],[f686,f61])).
% 1.69/0.66  fof(f61,plain,(
% 1.69/0.66    sK1 = sK3 | ~spl8_3),
% 1.69/0.66    inference(avatar_component_clause,[],[f60])).
% 1.69/0.66  fof(f686,plain,(
% 1.69/0.66    ( ! [X6,X5] : (r2_hidden(sK7(X5,X6,sK1),X5) | sK3 = k4_xboole_0(X5,X6)) ) | (~spl8_3 | ~spl8_12)),
% 1.69/0.66    inference(forward_demodulation,[],[f471,f61])).
% 1.69/0.66  fof(f471,plain,(
% 1.69/0.66    ( ! [X6,X5] : (r2_hidden(sK7(X5,X6,sK3),X5) | sK3 = k4_xboole_0(X5,X6)) ) | ~spl8_12),
% 1.69/0.66    inference(resolution,[],[f153,f35])).
% 1.69/0.66  fof(f153,plain,(
% 1.69/0.66    ( ! [X4] : (~r2_hidden(X4,sK3)) ) | ~spl8_12),
% 1.69/0.66    inference(avatar_component_clause,[],[f152])).
% 1.69/0.66  fof(f690,plain,(
% 1.69/0.66    ( ! [X8,X7] : (~r2_hidden(sK7(X7,X8,sK1),X8) | sK1 = k4_xboole_0(X7,X8)) ) | (~spl8_3 | ~spl8_12)),
% 1.69/0.66    inference(forward_demodulation,[],[f689,f61])).
% 1.69/0.66  fof(f689,plain,(
% 1.69/0.66    ( ! [X8,X7] : (~r2_hidden(sK7(X7,X8,sK1),X8) | sK3 = k4_xboole_0(X7,X8)) ) | (~spl8_3 | ~spl8_12)),
% 1.69/0.66    inference(forward_demodulation,[],[f472,f61])).
% 1.69/0.66  fof(f472,plain,(
% 1.69/0.66    ( ! [X8,X7] : (~r2_hidden(sK7(X7,X8,sK3),X8) | sK3 = k4_xboole_0(X7,X8)) ) | ~spl8_12),
% 1.69/0.66    inference(resolution,[],[f153,f36])).
% 1.69/0.66  fof(f589,plain,(
% 1.69/0.66    spl8_3 | ~spl8_12 | ~spl8_26),
% 1.69/0.66    inference(avatar_split_clause,[],[f559,f524,f152,f60])).
% 1.69/0.66  fof(f559,plain,(
% 1.69/0.66    sK1 = sK3 | (~spl8_12 | ~spl8_26)),
% 1.69/0.66    inference(resolution,[],[f548,f468])).
% 1.69/0.66  fof(f468,plain,(
% 1.69/0.66    ( ! [X2] : (r2_hidden(sK4(X2,sK3),X2) | sK3 = X2) ) | ~spl8_12),
% 1.69/0.66    inference(resolution,[],[f153,f21])).
% 1.69/0.66  fof(f21,plain,(
% 1.69/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 1.69/0.66    inference(cnf_transformation,[],[f13])).
% 1.69/0.66  fof(f13,plain,(
% 1.69/0.66    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.69/0.66    inference(ennf_transformation,[],[f4])).
% 1.69/0.66  fof(f4,axiom,(
% 1.69/0.66    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.69/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.69/0.66  fof(f548,plain,(
% 1.69/0.66    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl8_12 | ~spl8_26)),
% 1.69/0.66    inference(resolution,[],[f525,f153])).
% 1.69/0.66  fof(f526,plain,(
% 1.69/0.66    spl8_25 | spl8_26 | ~spl8_5),
% 1.69/0.66    inference(avatar_split_clause,[],[f79,f69,f524,f521])).
% 1.69/0.66  fof(f69,plain,(
% 1.69/0.66    spl8_5 <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.69/0.66  fof(f79,plain,(
% 1.69/0.66    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl8_5),
% 1.69/0.66    inference(resolution,[],[f74,f42])).
% 1.69/0.66  fof(f42,plain,(
% 1.69/0.66    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.69/0.66    inference(cnf_transformation,[],[f7])).
% 1.69/0.66  fof(f7,axiom,(
% 1.69/0.66    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.69/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.69/0.66  fof(f74,plain,(
% 1.69/0.66    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK3)) ) | ~spl8_5),
% 1.69/0.66    inference(superposition,[],[f41,f71])).
% 1.69/0.66  fof(f71,plain,(
% 1.69/0.66    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) | ~spl8_5),
% 1.69/0.66    inference(avatar_component_clause,[],[f69])).
% 1.69/0.66  fof(f41,plain,(
% 1.69/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.69/0.66    inference(cnf_transformation,[],[f7])).
% 1.69/0.66  fof(f459,plain,(
% 1.69/0.66    ~spl8_20 | spl8_4 | spl8_21),
% 1.69/0.66    inference(avatar_split_clause,[],[f454,f449,f64,f318])).
% 1.69/0.66  fof(f318,plain,(
% 1.69/0.66    spl8_20 <=> r1_tarski(sK2,sK0)),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.69/0.66  fof(f449,plain,(
% 1.69/0.66    spl8_21 <=> r2_xboole_0(sK2,sK0)),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.69/0.66  fof(f454,plain,(
% 1.69/0.66    sK0 = sK2 | ~r1_tarski(sK2,sK0) | spl8_21),
% 1.69/0.66    inference(resolution,[],[f451,f28])).
% 1.69/0.66  fof(f451,plain,(
% 1.69/0.66    ~r2_xboole_0(sK2,sK0) | spl8_21),
% 1.69/0.66    inference(avatar_component_clause,[],[f449])).
% 1.69/0.66  fof(f452,plain,(
% 1.69/0.66    ~spl8_21 | ~spl8_7),
% 1.69/0.66    inference(avatar_split_clause,[],[f447,f85,f449])).
% 1.69/0.66  fof(f85,plain,(
% 1.69/0.66    spl8_7 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.69/0.66  fof(f447,plain,(
% 1.69/0.66    ~r2_xboole_0(sK2,sK0) | ~spl8_7),
% 1.69/0.66    inference(duplicate_literal_removal,[],[f444])).
% 1.69/0.66  fof(f444,plain,(
% 1.69/0.66    ~r2_xboole_0(sK2,sK0) | ~r2_xboole_0(sK2,sK0) | ~spl8_7),
% 1.69/0.66    inference(resolution,[],[f435,f32])).
% 1.69/0.66  fof(f435,plain,(
% 1.69/0.66    ( ! [X2] : (~r2_hidden(sK6(sK2,X2),sK0) | ~r2_xboole_0(sK2,X2)) ) | ~spl8_7),
% 1.69/0.66    inference(resolution,[],[f86,f33])).
% 1.69/0.66  fof(f86,plain,(
% 1.69/0.66    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl8_7),
% 1.69/0.66    inference(avatar_component_clause,[],[f85])).
% 1.69/0.66  fof(f429,plain,(
% 1.69/0.66    spl8_2 | ~spl8_6),
% 1.69/0.66    inference(avatar_split_clause,[],[f397,f82,f55])).
% 1.69/0.66  fof(f82,plain,(
% 1.69/0.66    spl8_6 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.69/0.66  fof(f397,plain,(
% 1.69/0.66    k1_xboole_0 = sK1 | ~spl8_6),
% 1.69/0.66    inference(superposition,[],[f396,f20])).
% 1.69/0.66  fof(f396,plain,(
% 1.69/0.66    ( ! [X0] : (sK1 = k4_xboole_0(X0,X0)) ) | ~spl8_6),
% 1.69/0.66    inference(duplicate_literal_removal,[],[f386])).
% 1.69/0.66  fof(f386,plain,(
% 1.69/0.66    ( ! [X0] : (sK1 = k4_xboole_0(X0,X0) | sK1 = k4_xboole_0(X0,X0)) ) | ~spl8_6),
% 1.69/0.66    inference(resolution,[],[f253,f252])).
% 1.69/0.66  fof(f252,plain,(
% 1.69/0.66    ( ! [X6,X5] : (r2_hidden(sK7(X5,X6,sK1),X5) | sK1 = k4_xboole_0(X5,X6)) ) | ~spl8_6),
% 1.69/0.66    inference(resolution,[],[f83,f35])).
% 1.69/0.66  fof(f83,plain,(
% 1.69/0.66    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl8_6),
% 1.69/0.66    inference(avatar_component_clause,[],[f82])).
% 1.69/0.66  fof(f253,plain,(
% 1.69/0.66    ( ! [X8,X7] : (~r2_hidden(sK7(X7,X8,sK1),X8) | sK1 = k4_xboole_0(X7,X8)) ) | ~spl8_6),
% 1.69/0.66    inference(resolution,[],[f83,f36])).
% 1.69/0.66  fof(f321,plain,(
% 1.69/0.66    spl8_20 | ~spl8_11),
% 1.69/0.66    inference(avatar_split_clause,[],[f316,f149,f318])).
% 1.69/0.66  fof(f149,plain,(
% 1.69/0.66    spl8_11 <=> ! [X5] : (~r2_hidden(X5,sK2) | r2_hidden(X5,sK0))),
% 1.69/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.69/0.66  fof(f316,plain,(
% 1.69/0.66    r1_tarski(sK2,sK0) | ~spl8_11),
% 1.69/0.66    inference(duplicate_literal_removal,[],[f314])).
% 1.69/0.66  fof(f314,plain,(
% 1.69/0.66    r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0) | ~spl8_11),
% 1.69/0.66    inference(resolution,[],[f157,f24])).
% 1.69/0.66  fof(f157,plain,(
% 1.69/0.66    ( ! [X2] : (~r2_hidden(sK5(X2,sK0),sK2) | r1_tarski(X2,sK0)) ) | ~spl8_11),
% 1.69/0.66    inference(resolution,[],[f150,f25])).
% 1.69/0.66  fof(f150,plain,(
% 1.69/0.66    ( ! [X5] : (r2_hidden(X5,sK0) | ~r2_hidden(X5,sK2)) ) | ~spl8_11),
% 1.69/0.66    inference(avatar_component_clause,[],[f149])).
% 1.69/0.66  fof(f181,plain,(
% 1.69/0.66    spl8_14 | spl8_16 | ~spl8_5),
% 1.69/0.66    inference(avatar_split_clause,[],[f145,f69,f179,f165])).
% 1.69/0.66  fof(f145,plain,(
% 1.69/0.66    ( ! [X6,X7] : (~r2_hidden(X6,sK3) | ~r2_hidden(X7,sK2) | r2_hidden(X6,sK1)) ) | ~spl8_5),
% 1.69/0.66    inference(resolution,[],[f75,f41])).
% 1.69/0.66  fof(f75,plain,(
% 1.69/0.66    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) ) | ~spl8_5),
% 1.69/0.66    inference(superposition,[],[f42,f71])).
% 1.69/0.66  fof(f154,plain,(
% 1.69/0.66    spl8_11 | spl8_12 | ~spl8_5),
% 1.69/0.66    inference(avatar_split_clause,[],[f144,f69,f152,f149])).
% 1.69/0.66  fof(f144,plain,(
% 1.69/0.66    ( ! [X4,X5] : (~r2_hidden(X4,sK3) | ~r2_hidden(X5,sK2) | r2_hidden(X5,sK0)) ) | ~spl8_5),
% 1.69/0.66    inference(resolution,[],[f75,f40])).
% 1.69/0.66  fof(f40,plain,(
% 1.69/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.69/0.66    inference(cnf_transformation,[],[f7])).
% 1.69/0.66  fof(f87,plain,(
% 1.69/0.66    spl8_6 | spl8_7 | ~spl8_5),
% 1.69/0.66    inference(avatar_split_clause,[],[f77,f69,f85,f82])).
% 1.69/0.66  fof(f77,plain,(
% 1.69/0.66    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_5),
% 1.69/0.66    inference(resolution,[],[f73,f42])).
% 1.69/0.66  fof(f73,plain,(
% 1.69/0.66    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK2)) ) | ~spl8_5),
% 1.69/0.66    inference(superposition,[],[f40,f71])).
% 1.69/0.66  fof(f72,plain,(
% 1.69/0.66    spl8_5),
% 1.69/0.66    inference(avatar_split_clause,[],[f17,f69])).
% 1.69/0.66  fof(f17,plain,(
% 1.69/0.66    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.69/0.66    inference(cnf_transformation,[],[f12])).
% 1.69/0.66  fof(f12,plain,(
% 1.69/0.66    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.69/0.66    inference(flattening,[],[f11])).
% 1.69/0.66  fof(f11,plain,(
% 1.69/0.66    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.69/0.66    inference(ennf_transformation,[],[f10])).
% 1.69/0.66  fof(f10,negated_conjecture,(
% 1.69/0.66    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.69/0.66    inference(negated_conjecture,[],[f9])).
% 1.69/0.66  fof(f9,conjecture,(
% 1.69/0.66    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.69/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.69/0.66  fof(f67,plain,(
% 1.69/0.66    ~spl8_3 | ~spl8_4),
% 1.69/0.66    inference(avatar_split_clause,[],[f16,f64,f60])).
% 1.69/0.66  fof(f16,plain,(
% 1.69/0.66    sK0 != sK2 | sK1 != sK3),
% 1.69/0.66    inference(cnf_transformation,[],[f12])).
% 1.69/0.66  fof(f58,plain,(
% 1.69/0.66    ~spl8_2),
% 1.69/0.66    inference(avatar_split_clause,[],[f19,f55])).
% 1.69/0.66  fof(f19,plain,(
% 1.69/0.66    k1_xboole_0 != sK1),
% 1.69/0.66    inference(cnf_transformation,[],[f12])).
% 1.69/0.66  fof(f53,plain,(
% 1.69/0.66    ~spl8_1),
% 1.69/0.66    inference(avatar_split_clause,[],[f18,f50])).
% 1.69/0.66  fof(f18,plain,(
% 1.69/0.66    k1_xboole_0 != sK0),
% 1.69/0.66    inference(cnf_transformation,[],[f12])).
% 1.69/0.66  % SZS output end Proof for theBenchmark
% 1.69/0.66  % (11028)------------------------------
% 1.69/0.66  % (11028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.66  % (11028)Termination reason: Refutation
% 1.69/0.66  
% 1.69/0.66  % (11028)Memory used [KB]: 11129
% 1.69/0.66  % (11028)Time elapsed: 0.228 s
% 1.69/0.66  % (11028)------------------------------
% 1.69/0.66  % (11028)------------------------------
% 1.69/0.67  % (11004)Success in time 0.294 s
%------------------------------------------------------------------------------
