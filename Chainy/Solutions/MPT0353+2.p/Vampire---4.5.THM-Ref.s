%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0353+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 160 expanded)
%              Number of leaves         :   23 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  234 ( 419 expanded)
%              Number of equality atoms :   77 ( 137 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1065,f1070,f1075,f1112,f1133,f1159,f1216,f1411,f1454,f1459,f2115])).

fof(f2115,plain,
    ( spl25_8
    | ~ spl25_12
    | ~ spl25_13
    | ~ spl25_14 ),
    inference(avatar_contradiction_clause,[],[f2114])).

fof(f2114,plain,
    ( $false
    | spl25_8
    | ~ spl25_12
    | ~ spl25_13
    | ~ spl25_14 ),
    inference(subsumption_resolution,[],[f2113,f1006])).

fof(f1006,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1005])).

fof(f1005,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f821])).

fof(f821,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f660])).

fof(f660,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK14(X0,X1) != X0
            | ~ r2_hidden(sK14(X0,X1),X1) )
          & ( sK14(X0,X1) = X0
            | r2_hidden(sK14(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f658,f659])).

fof(f659,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK14(X0,X1) != X0
          | ~ r2_hidden(sK14(X0,X1),X1) )
        & ( sK14(X0,X1) = X0
          | r2_hidden(sK14(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f658,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f657])).

fof(f657,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f2113,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_tarski(k4_xboole_0(sK1,sK2)))
    | spl25_8
    | ~ spl25_12
    | ~ spl25_13
    | ~ spl25_14 ),
    inference(forward_demodulation,[],[f2112,f1484])).

fof(f1484,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl25_13
    | ~ spl25_14 ),
    inference(forward_demodulation,[],[f1483,f1453])).

fof(f1453,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl25_13 ),
    inference(avatar_component_clause,[],[f1451])).

fof(f1451,plain,
    ( spl25_13
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_13])])).

fof(f1483,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1)
    | ~ spl25_14 ),
    inference(forward_demodulation,[],[f1476,f802])).

fof(f802,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1476,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl25_14 ),
    inference(unit_resulting_resolution,[],[f1458,f732])).

fof(f732,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f510])).

fof(f510,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f458])).

fof(f458,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1458,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl25_14 ),
    inference(avatar_component_clause,[],[f1456])).

fof(f1456,plain,
    ( spl25_14
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_14])])).

fof(f2112,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_tarski(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)))
    | spl25_8
    | ~ spl25_12 ),
    inference(forward_demodulation,[],[f2111,f805])).

fof(f805,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2111,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_tarski(k4_xboole_0(k3_xboole_0(sK1,sK0),sK2)))
    | spl25_8
    | ~ spl25_12 ),
    inference(forward_demodulation,[],[f2097,f1447])).

fof(f1447,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k3_xboole_0(X0,sK0),sK2)
    | ~ spl25_12 ),
    inference(forward_demodulation,[],[f1413,f791])).

fof(f791,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1413,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(X0,k4_xboole_0(sK0,sK2))
    | ~ spl25_12 ),
    inference(unit_resulting_resolution,[],[f1410,f722])).

fof(f722,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f503])).

fof(f503,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f484])).

fof(f484,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1410,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl25_12 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f1408,plain,
    ( spl25_12
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_12])])).

fof(f2097,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_tarski(k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))))
    | spl25_8 ),
    inference(unit_resulting_resolution,[],[f1215,f1007])).

fof(f1007,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f820])).

fof(f820,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f660])).

fof(f1215,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | spl25_8 ),
    inference(avatar_component_clause,[],[f1213])).

fof(f1213,plain,
    ( spl25_8
  <=> k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_8])])).

fof(f1459,plain,
    ( spl25_14
    | ~ spl25_1
    | ~ spl25_5 ),
    inference(avatar_split_clause,[],[f1153,f1109,f1062,f1456])).

fof(f1062,plain,
    ( spl25_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_1])])).

fof(f1109,plain,
    ( spl25_5
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_5])])).

fof(f1153,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl25_1
    | ~ spl25_5 ),
    inference(backward_demodulation,[],[f1111,f1139])).

fof(f1139,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl25_1 ),
    inference(unit_resulting_resolution,[],[f1064,f732])).

fof(f1064,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl25_1 ),
    inference(avatar_component_clause,[],[f1062])).

fof(f1111,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl25_5 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f1454,plain,
    ( spl25_13
    | ~ spl25_1 ),
    inference(avatar_split_clause,[],[f1152,f1062,f1451])).

fof(f1152,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl25_1 ),
    inference(backward_demodulation,[],[f1134,f1139])).

fof(f1134,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl25_1 ),
    inference(unit_resulting_resolution,[],[f1064,f731])).

fof(f731,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f509])).

fof(f509,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f475])).

fof(f475,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1411,plain,
    ( spl25_12
    | ~ spl25_2
    | ~ spl25_6 ),
    inference(avatar_split_clause,[],[f1150,f1130,f1067,f1408])).

fof(f1067,plain,
    ( spl25_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_2])])).

fof(f1130,plain,
    ( spl25_6
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_6])])).

fof(f1150,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl25_2
    | ~ spl25_6 ),
    inference(backward_demodulation,[],[f1132,f1140])).

fof(f1140,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl25_2 ),
    inference(unit_resulting_resolution,[],[f1069,f732])).

fof(f1069,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl25_2 ),
    inference(avatar_component_clause,[],[f1067])).

fof(f1132,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl25_6 ),
    inference(avatar_component_clause,[],[f1130])).

fof(f1216,plain,
    ( ~ spl25_8
    | ~ spl25_1
    | spl25_7 ),
    inference(avatar_split_clause,[],[f1199,f1156,f1062,f1213])).

fof(f1156,plain,
    ( spl25_7
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_7])])).

fof(f1199,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | ~ spl25_1
    | spl25_7 ),
    inference(backward_demodulation,[],[f1158,f1190])).

fof(f1190,plain,
    ( ! [X0] : k7_subset_1(sK0,sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl25_1 ),
    inference(unit_resulting_resolution,[],[f1064,f734])).

fof(f734,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f512])).

fof(f512,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f482])).

fof(f482,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1158,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))
    | spl25_7 ),
    inference(avatar_component_clause,[],[f1156])).

fof(f1159,plain,
    ( ~ spl25_7
    | ~ spl25_2
    | spl25_3 ),
    inference(avatar_split_clause,[],[f1151,f1072,f1067,f1156])).

fof(f1072,plain,
    ( spl25_3
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_3])])).

fof(f1151,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))
    | ~ spl25_2
    | spl25_3 ),
    inference(backward_demodulation,[],[f1074,f1140])).

fof(f1074,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl25_3 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f1133,plain,
    ( spl25_6
    | ~ spl25_2 ),
    inference(avatar_split_clause,[],[f1104,f1067,f1130])).

fof(f1104,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl25_2 ),
    inference(unit_resulting_resolution,[],[f1069,f733])).

fof(f733,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f511])).

fof(f511,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f461])).

fof(f461,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1112,plain,
    ( spl25_5
    | ~ spl25_1 ),
    inference(avatar_split_clause,[],[f1103,f1062,f1109])).

fof(f1103,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl25_1 ),
    inference(unit_resulting_resolution,[],[f1064,f733])).

fof(f1075,plain,(
    ~ spl25_3 ),
    inference(avatar_split_clause,[],[f720,f1072])).

fof(f720,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f617])).

fof(f617,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f501,f616,f615])).

fof(f615,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f616,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f501,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f495])).

fof(f495,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f494])).

fof(f494,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f1070,plain,(
    spl25_2 ),
    inference(avatar_split_clause,[],[f719,f1067])).

fof(f719,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f617])).

fof(f1065,plain,(
    spl25_1 ),
    inference(avatar_split_clause,[],[f718,f1062])).

fof(f718,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f617])).
%------------------------------------------------------------------------------
