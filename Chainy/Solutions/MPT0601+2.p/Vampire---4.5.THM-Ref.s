%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0601+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 6.81s
% Output     : Refutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 119 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  227 ( 406 expanded)
%              Number of equality atoms :   39 (  89 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8988,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1538,f1539,f3749,f3877,f5050,f8984])).

fof(f8984,plain,
    ( spl60_1
    | spl60_2 ),
    inference(avatar_contradiction_clause,[],[f8983])).

fof(f8983,plain,
    ( $false
    | spl60_1
    | spl60_2 ),
    inference(subsumption_resolution,[],[f8884,f1536])).

fof(f1536,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl60_2 ),
    inference(avatar_component_clause,[],[f1535])).

fof(f1535,plain,
    ( spl60_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl60_2])])).

fof(f8884,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | spl60_1 ),
    inference(resolution,[],[f5108,f1195])).

fof(f1195,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1042])).

fof(f1042,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f880,f1041])).

fof(f1041,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f880,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f5108,plain,
    ( ! [X2] : ~ r2_hidden(X2,k11_relat_1(sK1,sK0))
    | spl60_1 ),
    inference(subsumption_resolution,[],[f5087,f1167])).

fof(f1167,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1031])).

fof(f1031,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1029,f1030])).

fof(f1030,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1029,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1028])).

fof(f1028,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f871])).

fof(f871,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f802])).

fof(f802,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f801])).

fof(f801,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f5087,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k11_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | spl60_1 ),
    inference(resolution,[],[f5057,f1172])).

fof(f1172,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1032])).

fof(f1032,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f873])).

fof(f873,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f800])).

fof(f800,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f5057,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK1)
    | spl60_1 ),
    inference(resolution,[],[f1533,f1503])).

fof(f1503,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f1315])).

fof(f1315,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1092])).

fof(f1092,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK26(X0,X1),X3),X0)
            | ~ r2_hidden(sK26(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK26(X0,X1),sK27(X0,X1)),X0)
            | r2_hidden(sK26(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK28(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26,sK27,sK28])],[f1088,f1091,f1090,f1089])).

fof(f1089,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK26(X0,X1),X3),X0)
          | ~ r2_hidden(sK26(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK26(X0,X1),X4),X0)
          | r2_hidden(sK26(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1090,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK26(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK26(X0,X1),sK27(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1091,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK28(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1088,plain,(
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
    inference(rectify,[],[f1087])).

fof(f1087,plain,(
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
    inference(nnf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1533,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl60_1 ),
    inference(avatar_component_clause,[],[f1531])).

fof(f1531,plain,
    ( spl60_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl60_1])])).

fof(f5050,plain,
    ( ~ spl60_1
    | ~ spl60_2
    | ~ spl60_11
    | ~ spl60_33 ),
    inference(avatar_contradiction_clause,[],[f5049])).

fof(f5049,plain,
    ( $false
    | ~ spl60_1
    | ~ spl60_2
    | ~ spl60_11
    | ~ spl60_33 ),
    inference(subsumption_resolution,[],[f5027,f1532])).

fof(f1532,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl60_1 ),
    inference(avatar_component_clause,[],[f1531])).

fof(f5027,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl60_2
    | ~ spl60_11
    | ~ spl60_33 ),
    inference(resolution,[],[f4855,f1504])).

fof(f1504,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK28(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f1314])).

fof(f1314,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK28(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1092])).

fof(f4855,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK1)
    | ~ spl60_2
    | ~ spl60_11
    | ~ spl60_33 ),
    inference(subsumption_resolution,[],[f4854,f1167])).

% (22511)Time limit reached!
% (22511)------------------------------
% (22511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22511)Termination reason: Time limit
% (22511)Termination phase: Saturation

% (22511)Memory used [KB]: 13688
% (22511)Time elapsed: 0.600 s
% (22511)------------------------------
% (22511)------------------------------
fof(f4854,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl60_2
    | ~ spl60_11
    | ~ spl60_33 ),
    inference(subsumption_resolution,[],[f4852,f3993])).

fof(f3993,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | ~ spl60_11
    | ~ spl60_33 ),
    inference(forward_demodulation,[],[f3932,f1883])).

fof(f1883,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl60_11 ),
    inference(avatar_component_clause,[],[f1882])).

fof(f1882,plain,
    ( spl60_11
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl60_11])])).

fof(f3932,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_relat_1(k1_xboole_0))
    | ~ spl60_33 ),
    inference(resolution,[],[f3634,f1423])).

fof(f1423,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f995])).

fof(f995,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f3634,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl60_33 ),
    inference(avatar_component_clause,[],[f3632])).

fof(f3632,plain,
    ( spl60_33
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl60_33])])).

fof(f4852,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(k4_tarski(sK0,X0),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl60_2 ),
    inference(superposition,[],[f1171,f1537])).

fof(f1537,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl60_2 ),
    inference(avatar_component_clause,[],[f1535])).

fof(f1171,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1032])).

fof(f3877,plain,(
    spl60_33 ),
    inference(avatar_contradiction_clause,[],[f3876])).

fof(f3876,plain,
    ( $false
    | spl60_33 ),
    inference(subsumption_resolution,[],[f3814,f1446])).

fof(f1446,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f3814,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl60_33 ),
    inference(resolution,[],[f3633,f1208])).

fof(f1208,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f888])).

fof(f888,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f676])).

fof(f676,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f3633,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | spl60_33 ),
    inference(avatar_component_clause,[],[f3632])).

fof(f3749,plain,
    ( spl60_11
    | ~ spl60_33 ),
    inference(avatar_contradiction_clause,[],[f3748])).

fof(f3748,plain,
    ( $false
    | spl60_11
    | ~ spl60_33 ),
    inference(subsumption_resolution,[],[f3700,f1884])).

fof(f1884,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl60_11 ),
    inference(avatar_component_clause,[],[f1882])).

fof(f3700,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl60_33 ),
    inference(resolution,[],[f3634,f1440])).

fof(f1440,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1006])).

fof(f1006,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f1539,plain,
    ( spl60_1
    | ~ spl60_2 ),
    inference(avatar_split_clause,[],[f1168,f1535,f1531])).

fof(f1168,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1031])).

fof(f1538,plain,
    ( ~ spl60_1
    | spl60_2 ),
    inference(avatar_split_clause,[],[f1169,f1535,f1531])).

fof(f1169,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1031])).
%------------------------------------------------------------------------------
