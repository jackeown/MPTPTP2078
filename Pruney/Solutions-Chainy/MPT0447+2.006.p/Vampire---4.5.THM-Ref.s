%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:09 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 496 expanded)
%              Number of leaves         :   32 ( 163 expanded)
%              Depth                    :   14
%              Number of atoms          :  302 ( 843 expanded)
%              Number of equality atoms :   41 ( 271 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f288,f292,f1329,f1335,f1345,f1347,f1915,f1960,f2389])).

fof(f2389,plain,
    ( ~ spl7_21
    | ~ spl7_28 ),
    inference(avatar_contradiction_clause,[],[f2376])).

fof(f2376,plain,
    ( $false
    | ~ spl7_21
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f46,f1959,f45,f1914,f495])).

fof(f495,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_relat_1(X3),X4)
      | r1_tarski(k3_relat_1(X3),X4)
      | ~ r1_tarski(k1_relat_1(X3),X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f87,f77])).

fof(f77,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1914,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f1912])).

fof(f1912,plain,
    ( spl7_21
  <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f45,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f1959,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f1957])).

fof(f1957,plain,
    ( spl7_28
  <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f46,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f1960,plain,
    ( ~ spl7_16
    | spl7_28
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f1953,f1332,f1957,f1322])).

fof(f1322,plain,
    ( spl7_16
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f1332,plain,
    ( spl7_18
  <=> r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f1953,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_18 ),
    inference(resolution,[],[f1943,f348])).

fof(f348,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,k1_relat_1(X4))
      | r1_tarski(X5,k3_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f189,f77])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f84,f80])).

fof(f80,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f56,f58,f58])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1943,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f1936,f1745])).

fof(f1745,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f1715,f97])).

fof(f97,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k6_subset_1(X2,X3))
      | k6_subset_1(X2,X3) = X2 ) ),
    inference(resolution,[],[f64,f78])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1715,plain,(
    ! [X6] : r1_tarski(X6,k6_subset_1(X6,k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f1668])).

fof(f1668,plain,(
    ! [X6] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X6,k6_subset_1(X6,k1_xboole_0)) ) ),
    inference(superposition,[],[f82,f1468])).

fof(f1468,plain,(
    ! [X9] : k1_xboole_0 = k6_subset_1(X9,k6_subset_1(X9,k1_xboole_0)) ),
    inference(resolution,[],[f1227,f96])).

fof(f96,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f64,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1227,plain,(
    ! [X66,X65] : r1_tarski(k6_subset_1(X65,k6_subset_1(X65,X66)),X66) ),
    inference(resolution,[],[f1058,f88])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1058,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X2),X1)
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(resolution,[],[f272,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f73,f57,f76])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f272,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0)))
      | r1_tarski(k6_subset_1(X2,X0),X1) ) ),
    inference(superposition,[],[f85,f80])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f72,f76,f57])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f57])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1936,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_xboole_0),k1_relat_1(sK1))
    | ~ spl7_18 ),
    inference(resolution,[],[f1334,f1058])).

fof(f1334,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f1332])).

fof(f1915,plain,
    ( ~ spl7_16
    | spl7_21
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f1908,f1326,f1912,f1322])).

fof(f1326,plain,
    ( spl7_17
  <=> r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f1908,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_17 ),
    inference(resolution,[],[f1898,f349])).

fof(f349,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X7,k2_relat_1(X6))
      | r1_tarski(X7,k3_relat_1(X6))
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f84,f77])).

fof(f1898,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f1891,f1745])).

fof(f1891,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k1_xboole_0),k2_relat_1(sK1))
    | ~ spl7_17 ),
    inference(resolution,[],[f1328,f1058])).

fof(f1328,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f1326])).

fof(f1347,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f1346])).

fof(f1346,plain,
    ( $false
    | spl7_16 ),
    inference(subsumption_resolution,[],[f43,f1324])).

fof(f1324,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f1322])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f1345,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f1344])).

fof(f1344,plain,
    ( $false
    | spl7_15 ),
    inference(subsumption_resolution,[],[f46,f1320])).

fof(f1320,plain,
    ( ~ v1_relat_1(sK0)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f1318])).

fof(f1318,plain,
    ( spl7_15
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1335,plain,
    ( ~ spl7_15
    | ~ spl7_16
    | spl7_18 ),
    inference(avatar_split_clause,[],[f1330,f1332,f1322,f1318])).

fof(f1330,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f1290,f278])).

fof(f278,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f277,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f277,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f263,f90])).

fof(f90,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f263,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f259])).

fof(f259,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f79,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(k1_tarski(X0),k1_tarski(X0),X1)) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f76])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f79,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_tarski(X0),k1_tarski(X0),X1)) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f1290,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f52,f1243])).

fof(f1243,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f1226,f96])).

fof(f1226,plain,(
    ! [X64] : r1_tarski(k6_subset_1(sK0,sK1),X64) ),
    inference(resolution,[],[f1058,f120])).

fof(f120,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),sK1) ),
    inference(resolution,[],[f114,f78])).

fof(f114,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,sK0)
      | r1_tarski(X7,sK1) ) ),
    inference(resolution,[],[f74,f44])).

fof(f44,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

fof(f1329,plain,
    ( ~ spl7_15
    | ~ spl7_16
    | spl7_17
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f1316,f286,f1326,f1322,f1318])).

fof(f286,plain,
    ( spl7_4
  <=> ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1316,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f1289,f300])).

fof(f300,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(resolution,[],[f287,f53])).

fof(f287,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f286])).

fof(f1289,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f51,f1243])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

fof(f292,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f92,f284])).

fof(f284,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl7_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f92,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f49,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f288,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f279,f286,f282])).

fof(f279,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f277,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (26035)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (26036)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (26051)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.51  % (26060)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (26034)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (26040)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (26054)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (26045)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (26033)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (26037)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (26056)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (26043)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (26031)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (26038)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (26059)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (26032)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (26041)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (26052)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (26046)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (26062)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (26058)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (26061)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (26039)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (26050)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (26057)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (26053)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (26042)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (26044)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (26047)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (26049)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.10/0.68  % (26034)Refutation not found, incomplete strategy% (26034)------------------------------
% 2.10/0.68  % (26034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.68  % (26034)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.68  
% 2.10/0.68  % (26034)Memory used [KB]: 6140
% 2.10/0.68  % (26034)Time elapsed: 0.268 s
% 2.10/0.68  % (26034)------------------------------
% 2.10/0.68  % (26034)------------------------------
% 2.10/0.70  % (26044)Refutation found. Thanks to Tanya!
% 2.10/0.70  % SZS status Theorem for theBenchmark
% 2.10/0.70  % SZS output start Proof for theBenchmark
% 2.10/0.70  fof(f2392,plain,(
% 2.10/0.70    $false),
% 2.10/0.70    inference(avatar_sat_refutation,[],[f288,f292,f1329,f1335,f1345,f1347,f1915,f1960,f2389])).
% 2.10/0.70  fof(f2389,plain,(
% 2.10/0.70    ~spl7_21 | ~spl7_28),
% 2.10/0.70    inference(avatar_contradiction_clause,[],[f2376])).
% 2.10/0.70  fof(f2376,plain,(
% 2.10/0.70    $false | (~spl7_21 | ~spl7_28)),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f46,f1959,f45,f1914,f495])).
% 2.10/0.70  fof(f495,plain,(
% 2.10/0.70    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(X3),X4) | r1_tarski(k3_relat_1(X3),X4) | ~r1_tarski(k1_relat_1(X3),X4) | ~v1_relat_1(X3)) )),
% 2.10/0.70    inference(superposition,[],[f87,f77])).
% 2.10/0.70  fof(f77,plain,(
% 2.10/0.70    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.10/0.70    inference(definition_unfolding,[],[f50,f76])).
% 2.10/0.70  fof(f76,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.10/0.70    inference(definition_unfolding,[],[f59,f58])).
% 2.10/0.70  fof(f58,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f13])).
% 2.10/0.70  fof(f13,axiom,(
% 2.10/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.10/0.70  fof(f59,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f15,axiom,(
% 2.10/0.70    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.10/0.70  fof(f50,plain,(
% 2.10/0.70    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f29])).
% 2.10/0.70  fof(f29,plain,(
% 2.10/0.70    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f20])).
% 2.10/0.70  fof(f20,axiom,(
% 2.10/0.70    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 2.10/0.70  fof(f87,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.10/0.70    inference(definition_unfolding,[],[f75,f76])).
% 2.10/0.70  fof(f75,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f42])).
% 2.10/0.70  fof(f42,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.10/0.70    inference(flattening,[],[f41])).
% 2.10/0.70  fof(f41,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.10/0.70    inference(ennf_transformation,[],[f11])).
% 2.10/0.70  fof(f11,axiom,(
% 2.10/0.70    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.10/0.70  fof(f1914,plain,(
% 2.10/0.70    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~spl7_21),
% 2.10/0.70    inference(avatar_component_clause,[],[f1912])).
% 2.10/0.70  fof(f1912,plain,(
% 2.10/0.70    spl7_21 <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 2.10/0.70  fof(f45,plain,(
% 2.10/0.70    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.10/0.70    inference(cnf_transformation,[],[f27])).
% 2.10/0.70  fof(f27,plain,(
% 2.10/0.70    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.10/0.70    inference(flattening,[],[f26])).
% 2.10/0.70  fof(f26,plain,(
% 2.10/0.70    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f25])).
% 2.10/0.70  fof(f25,negated_conjecture,(
% 2.10/0.70    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.10/0.70    inference(negated_conjecture,[],[f24])).
% 2.10/0.70  fof(f24,conjecture,(
% 2.10/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 2.10/0.70  fof(f1959,plain,(
% 2.10/0.70    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~spl7_28),
% 2.10/0.70    inference(avatar_component_clause,[],[f1957])).
% 2.10/0.70  fof(f1957,plain,(
% 2.10/0.70    spl7_28 <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 2.10/0.70  fof(f46,plain,(
% 2.10/0.70    v1_relat_1(sK0)),
% 2.10/0.70    inference(cnf_transformation,[],[f27])).
% 2.10/0.70  fof(f1960,plain,(
% 2.10/0.70    ~spl7_16 | spl7_28 | ~spl7_18),
% 2.10/0.70    inference(avatar_split_clause,[],[f1953,f1332,f1957,f1322])).
% 2.10/0.70  fof(f1322,plain,(
% 2.10/0.70    spl7_16 <=> v1_relat_1(sK1)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.10/0.70  fof(f1332,plain,(
% 2.10/0.70    spl7_18 <=> r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.10/0.70  fof(f1953,plain,(
% 2.10/0.70    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl7_18),
% 2.10/0.70    inference(resolution,[],[f1943,f348])).
% 2.10/0.70  fof(f348,plain,(
% 2.10/0.70    ( ! [X4,X5] : (~r1_tarski(X5,k1_relat_1(X4)) | r1_tarski(X5,k3_relat_1(X4)) | ~v1_relat_1(X4)) )),
% 2.10/0.70    inference(superposition,[],[f189,f77])).
% 2.10/0.70  fof(f189,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) | ~r1_tarski(X2,X1)) )),
% 2.10/0.70    inference(superposition,[],[f84,f80])).
% 2.10/0.70  fof(f80,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.10/0.70    inference(definition_unfolding,[],[f56,f58,f58])).
% 2.10/0.70  fof(f56,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f12])).
% 2.10/0.70  fof(f12,axiom,(
% 2.10/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.10/0.70  fof(f84,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.10/0.70    inference(definition_unfolding,[],[f71,f76])).
% 2.10/0.70  fof(f71,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f36])).
% 2.10/0.70  fof(f36,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.10/0.70    inference(ennf_transformation,[],[f5])).
% 2.10/0.70  fof(f5,axiom,(
% 2.10/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.10/0.70  fof(f1943,plain,(
% 2.10/0.70    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl7_18),
% 2.10/0.70    inference(forward_demodulation,[],[f1936,f1745])).
% 2.10/0.70  fof(f1745,plain,(
% 2.10/0.70    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 2.10/0.70    inference(resolution,[],[f1715,f97])).
% 2.10/0.70  fof(f97,plain,(
% 2.10/0.70    ( ! [X2,X3] : (~r1_tarski(X2,k6_subset_1(X2,X3)) | k6_subset_1(X2,X3) = X2) )),
% 2.10/0.70    inference(resolution,[],[f64,f78])).
% 2.10/0.70  fof(f78,plain,(
% 2.10/0.70    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.10/0.70    inference(definition_unfolding,[],[f54,f57])).
% 2.10/0.70  fof(f57,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f17])).
% 2.10/0.70  fof(f17,axiom,(
% 2.10/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.10/0.70  fof(f54,plain,(
% 2.10/0.70    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f8])).
% 2.10/0.70  fof(f8,axiom,(
% 2.10/0.70    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.10/0.70  fof(f64,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.10/0.70    inference(cnf_transformation,[],[f3])).
% 2.10/0.70  fof(f3,axiom,(
% 2.10/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.10/0.70  fof(f1715,plain,(
% 2.10/0.70    ( ! [X6] : (r1_tarski(X6,k6_subset_1(X6,k1_xboole_0))) )),
% 2.10/0.70    inference(trivial_inequality_removal,[],[f1668])).
% 2.10/0.70  fof(f1668,plain,(
% 2.10/0.70    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X6,k6_subset_1(X6,k1_xboole_0))) )),
% 2.10/0.70    inference(superposition,[],[f82,f1468])).
% 2.10/0.70  fof(f1468,plain,(
% 2.10/0.70    ( ! [X9] : (k1_xboole_0 = k6_subset_1(X9,k6_subset_1(X9,k1_xboole_0))) )),
% 2.10/0.70    inference(resolution,[],[f1227,f96])).
% 2.10/0.70  fof(f96,plain,(
% 2.10/0.70    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 2.10/0.70    inference(resolution,[],[f64,f48])).
% 2.10/0.70  fof(f48,plain,(
% 2.10/0.70    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f7])).
% 2.10/0.70  fof(f7,axiom,(
% 2.10/0.70    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.10/0.70  fof(f1227,plain,(
% 2.10/0.70    ( ! [X66,X65] : (r1_tarski(k6_subset_1(X65,k6_subset_1(X65,X66)),X66)) )),
% 2.10/0.70    inference(resolution,[],[f1058,f88])).
% 2.10/0.70  fof(f88,plain,(
% 2.10/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.10/0.70    inference(equality_resolution,[],[f63])).
% 2.10/0.70  fof(f63,plain,(
% 2.10/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.10/0.70    inference(cnf_transformation,[],[f3])).
% 2.10/0.70  fof(f1058,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X2),X1) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.10/0.70    inference(resolution,[],[f272,f86])).
% 2.10/0.70  fof(f86,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.10/0.70    inference(definition_unfolding,[],[f73,f57,f76])).
% 2.10/0.70  fof(f73,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f38])).
% 2.10/0.70  fof(f38,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.10/0.70    inference(ennf_transformation,[],[f10])).
% 2.10/0.70  fof(f10,axiom,(
% 2.10/0.70    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.10/0.70  fof(f272,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) | r1_tarski(k6_subset_1(X2,X0),X1)) )),
% 2.10/0.70    inference(superposition,[],[f85,f80])).
% 2.10/0.70  fof(f85,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.10/0.70    inference(definition_unfolding,[],[f72,f76,f57])).
% 2.10/0.70  fof(f72,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f37])).
% 2.10/0.70  fof(f37,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.10/0.70    inference(ennf_transformation,[],[f9])).
% 2.10/0.70  fof(f9,axiom,(
% 2.10/0.70    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.10/0.70  fof(f82,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 2.10/0.70    inference(definition_unfolding,[],[f70,f57])).
% 2.10/0.70  fof(f70,plain,(
% 2.10/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f4])).
% 2.10/0.70  fof(f4,axiom,(
% 2.10/0.70    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.10/0.70  fof(f1936,plain,(
% 2.10/0.70    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_xboole_0),k1_relat_1(sK1)) | ~spl7_18),
% 2.10/0.70    inference(resolution,[],[f1334,f1058])).
% 2.10/0.70  fof(f1334,plain,(
% 2.10/0.70    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) | ~spl7_18),
% 2.10/0.70    inference(avatar_component_clause,[],[f1332])).
% 2.10/0.70  fof(f1915,plain,(
% 2.10/0.70    ~spl7_16 | spl7_21 | ~spl7_17),
% 2.10/0.70    inference(avatar_split_clause,[],[f1908,f1326,f1912,f1322])).
% 2.10/0.70  fof(f1326,plain,(
% 2.10/0.70    spl7_17 <=> r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.10/0.70  fof(f1908,plain,(
% 2.10/0.70    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl7_17),
% 2.10/0.70    inference(resolution,[],[f1898,f349])).
% 2.10/0.70  fof(f349,plain,(
% 2.10/0.70    ( ! [X6,X7] : (~r1_tarski(X7,k2_relat_1(X6)) | r1_tarski(X7,k3_relat_1(X6)) | ~v1_relat_1(X6)) )),
% 2.10/0.70    inference(superposition,[],[f84,f77])).
% 2.10/0.70  fof(f1898,plain,(
% 2.10/0.70    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl7_17),
% 2.10/0.70    inference(forward_demodulation,[],[f1891,f1745])).
% 2.10/0.70  fof(f1891,plain,(
% 2.10/0.70    r1_tarski(k6_subset_1(k2_relat_1(sK0),k1_xboole_0),k2_relat_1(sK1)) | ~spl7_17),
% 2.10/0.70    inference(resolution,[],[f1328,f1058])).
% 2.10/0.70  fof(f1328,plain,(
% 2.10/0.70    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0) | ~spl7_17),
% 2.10/0.70    inference(avatar_component_clause,[],[f1326])).
% 2.10/0.70  fof(f1347,plain,(
% 2.10/0.70    spl7_16),
% 2.10/0.70    inference(avatar_contradiction_clause,[],[f1346])).
% 2.10/0.70  fof(f1346,plain,(
% 2.10/0.70    $false | spl7_16),
% 2.10/0.70    inference(subsumption_resolution,[],[f43,f1324])).
% 2.10/0.70  fof(f1324,plain,(
% 2.10/0.70    ~v1_relat_1(sK1) | spl7_16),
% 2.10/0.70    inference(avatar_component_clause,[],[f1322])).
% 2.10/0.70  fof(f43,plain,(
% 2.10/0.70    v1_relat_1(sK1)),
% 2.10/0.70    inference(cnf_transformation,[],[f27])).
% 2.10/0.70  fof(f1345,plain,(
% 2.10/0.70    spl7_15),
% 2.10/0.70    inference(avatar_contradiction_clause,[],[f1344])).
% 2.10/0.70  fof(f1344,plain,(
% 2.10/0.70    $false | spl7_15),
% 2.10/0.70    inference(subsumption_resolution,[],[f46,f1320])).
% 2.10/0.70  fof(f1320,plain,(
% 2.10/0.70    ~v1_relat_1(sK0) | spl7_15),
% 2.10/0.70    inference(avatar_component_clause,[],[f1318])).
% 2.10/0.70  fof(f1318,plain,(
% 2.10/0.70    spl7_15 <=> v1_relat_1(sK0)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.10/0.70  fof(f1335,plain,(
% 2.10/0.70    ~spl7_15 | ~spl7_16 | spl7_18),
% 2.10/0.70    inference(avatar_split_clause,[],[f1330,f1332,f1322,f1318])).
% 2.10/0.70  fof(f1330,plain,(
% 2.10/0.70    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 2.10/0.70    inference(forward_demodulation,[],[f1290,f278])).
% 2.10/0.70  fof(f278,plain,(
% 2.10/0.70    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.10/0.70    inference(resolution,[],[f277,f53])).
% 2.10/0.70  fof(f53,plain,(
% 2.10/0.70    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.10/0.70    inference(cnf_transformation,[],[f32])).
% 2.10/0.70  fof(f32,plain,(
% 2.10/0.70    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.10/0.70    inference(ennf_transformation,[],[f2])).
% 2.10/0.70  fof(f2,axiom,(
% 2.10/0.70    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.10/0.70  fof(f277,plain,(
% 2.10/0.70    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 2.10/0.70    inference(resolution,[],[f263,f90])).
% 2.10/0.70  fof(f90,plain,(
% 2.10/0.70    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 2.10/0.70    inference(equality_resolution,[],[f66])).
% 2.10/0.70  fof(f66,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 2.10/0.70    inference(cnf_transformation,[],[f19])).
% 2.10/0.70  fof(f19,axiom,(
% 2.10/0.70    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 2.10/0.70  fof(f263,plain,(
% 2.10/0.70    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.10/0.70    inference(equality_resolution,[],[f259])).
% 2.10/0.70  fof(f259,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~r2_hidden(X0,X1)) )),
% 2.10/0.70    inference(superposition,[],[f79,f81])).
% 2.10/0.70  fof(f81,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k1_tarski(X0),k1_tarski(X0),X1)) = X1 | ~r2_hidden(X0,X1)) )),
% 2.10/0.70    inference(definition_unfolding,[],[f61,f76])).
% 2.10/0.70  fof(f61,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 2.10/0.70    inference(cnf_transformation,[],[f35])).
% 2.10/0.70  fof(f35,plain,(
% 2.10/0.70    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 2.10/0.70    inference(ennf_transformation,[],[f14])).
% 2.10/0.70  fof(f14,axiom,(
% 2.10/0.70    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 2.10/0.70  fof(f79,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_tarski(X0),k1_tarski(X0),X1))) )),
% 2.10/0.70    inference(definition_unfolding,[],[f55,f76])).
% 2.10/0.70  fof(f55,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f16])).
% 2.10/0.70  fof(f16,axiom,(
% 2.10/0.70    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 2.10/0.70  fof(f1290,plain,(
% 2.10/0.70    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 2.10/0.70    inference(superposition,[],[f52,f1243])).
% 2.10/0.70  fof(f1243,plain,(
% 2.10/0.70    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 2.10/0.70    inference(resolution,[],[f1226,f96])).
% 2.10/0.70  fof(f1226,plain,(
% 2.10/0.70    ( ! [X64] : (r1_tarski(k6_subset_1(sK0,sK1),X64)) )),
% 2.10/0.70    inference(resolution,[],[f1058,f120])).
% 2.10/0.70  fof(f120,plain,(
% 2.10/0.70    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),sK1)) )),
% 2.10/0.70    inference(resolution,[],[f114,f78])).
% 2.10/0.70  fof(f114,plain,(
% 2.10/0.70    ( ! [X7] : (~r1_tarski(X7,sK0) | r1_tarski(X7,sK1)) )),
% 2.10/0.70    inference(resolution,[],[f74,f44])).
% 2.10/0.70  fof(f44,plain,(
% 2.10/0.70    r1_tarski(sK0,sK1)),
% 2.10/0.70    inference(cnf_transformation,[],[f27])).
% 2.10/0.70  fof(f74,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f40])).
% 2.10/0.70  fof(f40,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.10/0.70    inference(flattening,[],[f39])).
% 2.10/0.70  fof(f39,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.10/0.70    inference(ennf_transformation,[],[f6])).
% 2.10/0.70  fof(f6,axiom,(
% 2.10/0.70    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.10/0.70  fof(f52,plain,(
% 2.10/0.70    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f31])).
% 2.10/0.70  fof(f31,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f21])).
% 2.10/0.70  fof(f21,axiom,(
% 2.10/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
% 2.10/0.70  fof(f1329,plain,(
% 2.10/0.70    ~spl7_15 | ~spl7_16 | spl7_17 | ~spl7_4),
% 2.10/0.70    inference(avatar_split_clause,[],[f1316,f286,f1326,f1322,f1318])).
% 2.10/0.70  fof(f286,plain,(
% 2.10/0.70    spl7_4 <=> ! [X0] : ~r2_hidden(X0,k2_relat_1(k1_xboole_0))),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.10/0.70  fof(f1316,plain,(
% 2.10/0.70    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~spl7_4),
% 2.10/0.70    inference(forward_demodulation,[],[f1289,f300])).
% 2.10/0.70  fof(f300,plain,(
% 2.10/0.70    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl7_4),
% 2.10/0.70    inference(resolution,[],[f287,f53])).
% 2.10/0.70  fof(f287,plain,(
% 2.10/0.70    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | ~spl7_4),
% 2.10/0.70    inference(avatar_component_clause,[],[f286])).
% 2.10/0.70  fof(f1289,plain,(
% 2.10/0.70    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 2.10/0.70    inference(superposition,[],[f51,f1243])).
% 2.10/0.70  fof(f51,plain,(
% 2.10/0.70    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f30])).
% 2.10/0.70  fof(f30,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f23])).
% 2.10/0.70  fof(f23,axiom,(
% 2.10/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
% 2.10/0.70  fof(f292,plain,(
% 2.10/0.70    spl7_3),
% 2.10/0.70    inference(avatar_contradiction_clause,[],[f289])).
% 2.10/0.70  fof(f289,plain,(
% 2.10/0.70    $false | spl7_3),
% 2.10/0.70    inference(subsumption_resolution,[],[f92,f284])).
% 2.10/0.70  fof(f284,plain,(
% 2.10/0.70    ~v1_relat_1(k1_xboole_0) | spl7_3),
% 2.10/0.70    inference(avatar_component_clause,[],[f282])).
% 2.10/0.70  fof(f282,plain,(
% 2.10/0.70    spl7_3 <=> v1_relat_1(k1_xboole_0)),
% 2.10/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.10/0.70  fof(f92,plain,(
% 2.10/0.70    v1_relat_1(k1_xboole_0)),
% 2.10/0.70    inference(resolution,[],[f49,f47])).
% 2.10/0.70  fof(f47,plain,(
% 2.10/0.70    v1_xboole_0(k1_xboole_0)),
% 2.10/0.70    inference(cnf_transformation,[],[f1])).
% 2.10/0.70  fof(f1,axiom,(
% 2.10/0.70    v1_xboole_0(k1_xboole_0)),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.10/0.70  fof(f49,plain,(
% 2.10/0.70    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f28])).
% 2.10/0.70  fof(f28,plain,(
% 2.10/0.70    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f18])).
% 2.10/0.70  fof(f18,axiom,(
% 2.10/0.70    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 2.10/0.70  fof(f288,plain,(
% 2.10/0.70    ~spl7_3 | spl7_4),
% 2.10/0.70    inference(avatar_split_clause,[],[f279,f286,f282])).
% 2.10/0.70  fof(f279,plain,(
% 2.10/0.70    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 2.10/0.70    inference(resolution,[],[f277,f60])).
% 2.10/0.70  fof(f60,plain,(
% 2.10/0.70    ( ! [X0,X1] : (r2_hidden(sK3(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f34])).
% 2.10/0.70  fof(f34,plain,(
% 2.10/0.70    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.10/0.70    inference(flattening,[],[f33])).
% 2.10/0.70  fof(f33,plain,(
% 2.10/0.70    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.10/0.70    inference(ennf_transformation,[],[f22])).
% 2.10/0.70  fof(f22,axiom,(
% 2.10/0.70    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 2.10/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 2.10/0.70  % SZS output end Proof for theBenchmark
% 2.10/0.70  % (26044)------------------------------
% 2.10/0.70  % (26044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.70  % (26044)Termination reason: Refutation
% 2.10/0.70  
% 2.10/0.70  % (26044)Memory used [KB]: 7675
% 2.10/0.70  % (26044)Time elapsed: 0.297 s
% 2.10/0.70  % (26044)------------------------------
% 2.10/0.70  % (26044)------------------------------
% 2.67/0.72  % (26024)Success in time 0.364 s
%------------------------------------------------------------------------------
