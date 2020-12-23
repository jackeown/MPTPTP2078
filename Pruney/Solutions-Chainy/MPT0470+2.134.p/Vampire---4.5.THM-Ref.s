%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:03 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 166 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  203 ( 423 expanded)
%              Number of equality atoms :   81 ( 238 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1460,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f186,f1312,f1337,f1429,f1454])).

fof(f1454,plain,
    ( spl9_2
    | ~ spl9_27 ),
    inference(avatar_contradiction_clause,[],[f1453])).

fof(f1453,plain,
    ( $false
    | spl9_2
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f1452,f185])).

fof(f185,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl9_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f1452,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f1451,f104])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f1451,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f1450,f165])).

fof(f165,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1450,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f1434,f1316])).

fof(f1316,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f1126,f98])).

fof(f98,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f1126,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f1125,f102])).

fof(f102,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1125,plain,(
    ! [X0] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f1124,f765])).

fof(f765,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f118,f165])).

fof(f118,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1124,plain,(
    ! [X0] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1122,f777])).

fof(f777,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f776])).

fof(f776,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f137,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f137,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1122,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f115,f101])).

fof(f101,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f1434,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))
    | ~ spl9_27 ),
    inference(resolution,[],[f1415,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f1415,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f1414])).

fof(f1414,plain,
    ( spl9_27
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f1429,plain,(
    spl9_27 ),
    inference(avatar_contradiction_clause,[],[f1428])).

fof(f1428,plain,
    ( $false
    | spl9_27 ),
    inference(subsumption_resolution,[],[f1427,f98])).

fof(f1427,plain,
    ( ~ v1_relat_1(sK0)
    | spl9_27 ),
    inference(subsumption_resolution,[],[f1426,f765])).

fof(f1426,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl9_27 ),
    inference(resolution,[],[f1416,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f1416,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl9_27 ),
    inference(avatar_component_clause,[],[f1414])).

fof(f1337,plain,
    ( spl9_1
    | ~ spl9_23 ),
    inference(avatar_contradiction_clause,[],[f1336])).

fof(f1336,plain,
    ( $false
    | spl9_1
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1335,f181])).

fof(f181,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl9_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f1335,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f1334,f104])).

fof(f1334,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f1333,f166])).

fof(f166,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f1333,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f1317,f1290])).

fof(f1290,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f1118,f98])).

fof(f1118,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(forward_demodulation,[],[f1117,f101])).

fof(f1117,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f1116,f765])).

fof(f1116,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f1114,f777])).

fof(f1114,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f114,f102])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f1317,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ spl9_23 ),
    inference(resolution,[],[f1299,f107])).

fof(f1299,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f1298])).

fof(f1298,plain,
    ( spl9_23
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f1312,plain,(
    spl9_23 ),
    inference(avatar_contradiction_clause,[],[f1311])).

fof(f1311,plain,
    ( $false
    | spl9_23 ),
    inference(subsumption_resolution,[],[f1310,f765])).

fof(f1310,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl9_23 ),
    inference(subsumption_resolution,[],[f1309,f98])).

fof(f1309,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl9_23 ),
    inference(resolution,[],[f1300,f124])).

fof(f1300,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl9_23 ),
    inference(avatar_component_clause,[],[f1298])).

fof(f186,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f99,f183,f179])).

fof(f99,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (21655)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (21669)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (21663)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (21661)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (21671)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (21657)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (21653)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (21651)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (21669)Refutation not found, incomplete strategy% (21669)------------------------------
% 0.20/0.51  % (21669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21669)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  % (21656)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  
% 0.20/0.51  % (21669)Memory used [KB]: 10746
% 0.20/0.51  % (21669)Time elapsed: 0.056 s
% 0.20/0.51  % (21669)------------------------------
% 0.20/0.51  % (21669)------------------------------
% 0.20/0.51  % (21652)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (21650)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (21648)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (21649)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (21666)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (21665)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (21670)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (21658)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (21668)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (21647)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (21664)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (21674)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (21675)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (21673)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (21662)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (21676)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (21667)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (21672)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (21660)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (21659)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.56  % (21654)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.56  % (21664)Refutation not found, incomplete strategy% (21664)------------------------------
% 1.49/0.56  % (21664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (21664)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (21664)Memory used [KB]: 10618
% 1.49/0.56  % (21664)Time elapsed: 0.152 s
% 1.49/0.56  % (21664)------------------------------
% 1.49/0.56  % (21664)------------------------------
% 1.49/0.56  % (21655)Refutation found. Thanks to Tanya!
% 1.49/0.56  % SZS status Theorem for theBenchmark
% 1.49/0.56  % SZS output start Proof for theBenchmark
% 1.49/0.56  fof(f1460,plain,(
% 1.49/0.56    $false),
% 1.49/0.56    inference(avatar_sat_refutation,[],[f186,f1312,f1337,f1429,f1454])).
% 1.49/0.56  fof(f1454,plain,(
% 1.49/0.56    spl9_2 | ~spl9_27),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f1453])).
% 1.49/0.56  fof(f1453,plain,(
% 1.49/0.56    $false | (spl9_2 | ~spl9_27)),
% 1.49/0.56    inference(subsumption_resolution,[],[f1452,f185])).
% 1.49/0.56  fof(f185,plain,(
% 1.49/0.56    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl9_2),
% 1.49/0.56    inference(avatar_component_clause,[],[f183])).
% 1.49/0.56  fof(f183,plain,(
% 1.49/0.56    spl9_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.49/0.56  fof(f1452,plain,(
% 1.49/0.56    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl9_27),
% 1.49/0.56    inference(forward_demodulation,[],[f1451,f104])).
% 1.49/0.56  fof(f104,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.49/0.56  fof(f1451,plain,(
% 1.49/0.56    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl9_27),
% 1.49/0.56    inference(forward_demodulation,[],[f1450,f165])).
% 1.49/0.56  fof(f165,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.49/0.56    inference(equality_resolution,[],[f136])).
% 1.49/0.56  fof(f136,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.49/0.56    inference(cnf_transformation,[],[f86])).
% 1.49/0.56  fof(f86,plain,(
% 1.49/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.49/0.56    inference(flattening,[],[f85])).
% 1.49/0.56  fof(f85,plain,(
% 1.49/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.49/0.56    inference(nnf_transformation,[],[f11])).
% 1.49/0.56  fof(f11,axiom,(
% 1.49/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.49/0.56  fof(f1450,plain,(
% 1.49/0.56    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) | ~spl9_27),
% 1.49/0.56    inference(forward_demodulation,[],[f1434,f1316])).
% 1.49/0.56  fof(f1316,plain,(
% 1.49/0.56    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.49/0.56    inference(resolution,[],[f1126,f98])).
% 1.49/0.56  fof(f98,plain,(
% 1.49/0.56    v1_relat_1(sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f67])).
% 1.49/0.56  fof(f67,plain,(
% 1.49/0.56    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f66])).
% 1.49/0.56  fof(f66,plain,(
% 1.49/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f39,plain,(
% 1.49/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f37])).
% 1.49/0.56  fof(f37,negated_conjecture,(
% 1.49/0.56    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.49/0.56    inference(negated_conjecture,[],[f36])).
% 1.49/0.56  fof(f36,conjecture,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.49/0.56  fof(f1126,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 1.49/0.56    inference(forward_demodulation,[],[f1125,f102])).
% 1.49/0.56  fof(f102,plain,(
% 1.49/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.49/0.56    inference(cnf_transformation,[],[f35])).
% 1.49/0.56  fof(f35,axiom,(
% 1.49/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.49/0.56  fof(f1125,plain,(
% 1.49/0.56    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f1124,f765])).
% 1.49/0.56  fof(f765,plain,(
% 1.49/0.56    v1_relat_1(k1_xboole_0)),
% 1.49/0.56    inference(superposition,[],[f118,f165])).
% 1.49/0.56  fof(f118,plain,(
% 1.49/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f21])).
% 1.49/0.56  fof(f21,axiom,(
% 1.49/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.49/0.56  fof(f1124,plain,(
% 1.49/0.56    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f1122,f777])).
% 1.49/0.56  fof(f777,plain,(
% 1.49/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.56    inference(trivial_inequality_removal,[],[f776])).
% 1.49/0.56  fof(f776,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.56    inference(superposition,[],[f137,f103])).
% 1.49/0.56  fof(f103,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f8])).
% 1.49/0.56  fof(f8,axiom,(
% 1.49/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.49/0.56  fof(f137,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f87])).
% 1.49/0.56  fof(f87,plain,(
% 1.49/0.56    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.49/0.56    inference(nnf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.49/0.56  fof(f1122,plain,(
% 1.49/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.49/0.56    inference(superposition,[],[f115,f101])).
% 1.49/0.56  fof(f101,plain,(
% 1.49/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.49/0.56    inference(cnf_transformation,[],[f35])).
% 1.49/0.56  fof(f115,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f51])).
% 1.49/0.56  fof(f51,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f50])).
% 1.49/0.56  fof(f50,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f31])).
% 1.49/0.56  fof(f31,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 1.49/0.56  fof(f1434,plain,(
% 1.49/0.56    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))) | ~spl9_27),
% 1.49/0.56    inference(resolution,[],[f1415,f107])).
% 1.49/0.56  fof(f107,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f40])).
% 1.49/0.56  fof(f40,plain,(
% 1.49/0.56    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f26])).
% 1.49/0.56  fof(f26,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 1.49/0.56  fof(f1415,plain,(
% 1.49/0.56    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl9_27),
% 1.49/0.56    inference(avatar_component_clause,[],[f1414])).
% 1.49/0.56  fof(f1414,plain,(
% 1.49/0.56    spl9_27 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 1.49/0.56  fof(f1429,plain,(
% 1.49/0.56    spl9_27),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f1428])).
% 1.49/0.56  fof(f1428,plain,(
% 1.49/0.56    $false | spl9_27),
% 1.49/0.56    inference(subsumption_resolution,[],[f1427,f98])).
% 1.49/0.56  fof(f1427,plain,(
% 1.49/0.56    ~v1_relat_1(sK0) | spl9_27),
% 1.49/0.56    inference(subsumption_resolution,[],[f1426,f765])).
% 1.49/0.56  fof(f1426,plain,(
% 1.49/0.56    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl9_27),
% 1.49/0.56    inference(resolution,[],[f1416,f124])).
% 1.49/0.56  fof(f124,plain,(
% 1.49/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f60])).
% 1.49/0.56  fof(f60,plain,(
% 1.49/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f59])).
% 1.49/0.56  fof(f59,plain,(
% 1.49/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f20])).
% 1.49/0.56  fof(f20,axiom,(
% 1.49/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.49/0.56  fof(f1416,plain,(
% 1.49/0.56    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl9_27),
% 1.49/0.56    inference(avatar_component_clause,[],[f1414])).
% 1.49/0.56  fof(f1337,plain,(
% 1.49/0.56    spl9_1 | ~spl9_23),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f1336])).
% 1.49/0.56  fof(f1336,plain,(
% 1.49/0.56    $false | (spl9_1 | ~spl9_23)),
% 1.49/0.56    inference(subsumption_resolution,[],[f1335,f181])).
% 1.49/0.56  fof(f181,plain,(
% 1.49/0.56    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl9_1),
% 1.49/0.56    inference(avatar_component_clause,[],[f179])).
% 1.49/0.56  fof(f179,plain,(
% 1.49/0.56    spl9_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.49/0.56  fof(f1335,plain,(
% 1.49/0.56    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~spl9_23),
% 1.49/0.56    inference(forward_demodulation,[],[f1334,f104])).
% 1.49/0.56  fof(f1334,plain,(
% 1.49/0.56    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) | ~spl9_23),
% 1.49/0.56    inference(forward_demodulation,[],[f1333,f166])).
% 1.49/0.56  fof(f166,plain,(
% 1.49/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.49/0.56    inference(equality_resolution,[],[f135])).
% 1.49/0.56  fof(f135,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f86])).
% 1.49/0.56  fof(f1333,plain,(
% 1.49/0.56    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | ~spl9_23),
% 1.49/0.56    inference(forward_demodulation,[],[f1317,f1290])).
% 1.49/0.56  fof(f1290,plain,(
% 1.49/0.56    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.49/0.56    inference(resolution,[],[f1118,f98])).
% 1.49/0.56  fof(f1118,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.49/0.56    inference(forward_demodulation,[],[f1117,f101])).
% 1.49/0.56  fof(f1117,plain,(
% 1.49/0.56    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f1116,f765])).
% 1.49/0.56  fof(f1116,plain,(
% 1.49/0.56    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f1114,f777])).
% 1.49/0.56  fof(f1114,plain,(
% 1.49/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.49/0.56    inference(superposition,[],[f114,f102])).
% 1.49/0.56  fof(f114,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f49])).
% 1.49/0.56  fof(f49,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f48])).
% 1.49/0.56  fof(f48,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f30])).
% 1.49/0.56  fof(f30,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.49/0.56  fof(f1317,plain,(
% 1.49/0.56    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | ~spl9_23),
% 1.49/0.56    inference(resolution,[],[f1299,f107])).
% 1.49/0.56  fof(f1299,plain,(
% 1.49/0.56    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl9_23),
% 1.49/0.56    inference(avatar_component_clause,[],[f1298])).
% 1.49/0.56  fof(f1298,plain,(
% 1.49/0.56    spl9_23 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 1.49/0.56  fof(f1312,plain,(
% 1.49/0.56    spl9_23),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f1311])).
% 1.49/0.56  fof(f1311,plain,(
% 1.49/0.56    $false | spl9_23),
% 1.49/0.56    inference(subsumption_resolution,[],[f1310,f765])).
% 1.49/0.56  fof(f1310,plain,(
% 1.49/0.56    ~v1_relat_1(k1_xboole_0) | spl9_23),
% 1.49/0.56    inference(subsumption_resolution,[],[f1309,f98])).
% 1.49/0.56  fof(f1309,plain,(
% 1.49/0.56    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl9_23),
% 1.49/0.56    inference(resolution,[],[f1300,f124])).
% 1.49/0.56  fof(f1300,plain,(
% 1.49/0.56    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl9_23),
% 1.49/0.56    inference(avatar_component_clause,[],[f1298])).
% 1.49/0.56  fof(f186,plain,(
% 1.49/0.56    ~spl9_1 | ~spl9_2),
% 1.49/0.56    inference(avatar_split_clause,[],[f99,f183,f179])).
% 1.49/0.56  fof(f99,plain,(
% 1.49/0.56    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f67])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (21655)------------------------------
% 1.49/0.56  % (21655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (21655)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (21655)Memory used [KB]: 11513
% 1.49/0.56  % (21655)Time elapsed: 0.134 s
% 1.49/0.56  % (21655)------------------------------
% 1.49/0.56  % (21655)------------------------------
% 1.49/0.57  % (21644)Success in time 0.206 s
%------------------------------------------------------------------------------
