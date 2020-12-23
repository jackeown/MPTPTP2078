%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0350+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 224 expanded)
%              Number of leaves         :   15 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  104 ( 345 expanded)
%              Number of equality atoms :   56 ( 196 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1670,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1649])).

fof(f1649,plain,(
    k2_zfmisc_1(sK0,sK0) != k2_zfmisc_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f1516,f1626])).

fof(f1626,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1625,f1045])).

fof(f1045,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f742,f1041])).

fof(f1041,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f740,f834])).

fof(f834,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f455])).

fof(f455,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f740,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f484])).

fof(f484,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f742,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f1625,plain,(
    k3_subset_1(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1615,f1623])).

fof(f1623,plain,(
    k1_xboole_0 = k3_subset_1(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1616,f904])).

fof(f904,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f1616,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1265,f738])).

fof(f738,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f505])).

fof(f505,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f457])).

fof(f457,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1265,plain,(
    m1_subset_1(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f1256,f1264])).

fof(f1264,plain,(
    k4_subset_1(sK0,sK0,sK1) = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1263,f770])).

fof(f770,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1263,plain,(
    k4_subset_1(sK0,sK0,sK1) = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1262,f1045])).

fof(f1262,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,k1_xboole_0),sK1) = k2_xboole_0(sK1,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1234,f770])).

fof(f1234,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,k1_xboole_0),sK1) = k2_xboole_0(k3_subset_1(sK0,k1_xboole_0),sK1) ),
    inference(unit_resulting_resolution,[],[f1044,f727,f730])).

fof(f730,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f497])).

fof(f497,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f496])).

fof(f496,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f475])).

fof(f475,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f727,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f629])).

fof(f629,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f493,f628])).

fof(f628,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f493,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f486])).

fof(f486,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f485])).

fof(f485,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f1044,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f741,f1041])).

fof(f741,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f459])).

fof(f459,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f1256,plain,(
    m1_subset_1(k4_subset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f1244,f1045])).

fof(f1244,plain,(
    m1_subset_1(k4_subset_1(sK0,k3_subset_1(sK0,k1_xboole_0),sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1044,f727,f731])).

fof(f731,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f499])).

fof(f499,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f498])).

fof(f498,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f461])).

fof(f461,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1615,plain,(
    k2_xboole_0(sK0,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f1265,f737])).

fof(f737,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f504])).

fof(f504,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f471])).

fof(f471,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1516,plain,(
    k2_zfmisc_1(sK0,sK0) != k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1353,f1495])).

fof(f1495,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1494,f770])).

fof(f1494,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1462,f830])).

fof(f830,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1462,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f727,f1253,f730])).

fof(f1253,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f1249,f1248])).

fof(f1248,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f727,f738])).

fof(f1249,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f727,f739])).

fof(f739,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f506])).

fof(f506,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f460])).

fof(f460,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1353,plain,(
    k2_zfmisc_1(sK0,sK0) != k2_zfmisc_1(k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)),k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f1254,f993])).

fof(f993,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) != k2_zfmisc_1(X1,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f606])).

fof(f606,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k2_zfmisc_1(X0,X0) != k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f331])).

fof(f331,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f1254,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1216,f1248])).

fof(f1216,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1043,f1045])).

fof(f1043,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_subset_1(sK0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f728,f1041])).

fof(f728,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f629])).
%------------------------------------------------------------------------------
