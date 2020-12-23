%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:28 EST 2020

% Result     : Theorem 5.10s
% Output     : Refutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 745 expanded)
%              Number of leaves         :   40 ( 247 expanded)
%              Depth                    :   16
%              Number of atoms          :  380 (1168 expanded)
%              Number of equality atoms :  138 ( 717 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1418,f1454,f1498,f2425,f2427,f4601,f4611,f4720,f4770,f4775,f4779,f5137,f5165,f5227])).

fof(f5227,plain,(
    ~ spl6_83 ),
    inference(avatar_contradiction_clause,[],[f5166])).

fof(f5166,plain,
    ( $false
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f247,f1497])).

fof(f1497,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f1495])).

fof(f1495,plain,
    ( spl6_83
  <=> k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f247,plain,(
    k1_zfmisc_1(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f119,f121])).

fof(f121,plain,(
    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f61,f117])).

fof(f117,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f114])).

fof(f114,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f104,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f106,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f107,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f108,f109])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f106,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f104,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f119,plain,(
    k7_setfam_1(sK0,sK1) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f60,f117])).

fof(f60,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_tarski(X0) = X1
         => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f35,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_tarski(X0) = X1
       => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).

fof(f5165,plain,
    ( ~ spl6_173
    | spl6_83
    | ~ spl6_82 ),
    inference(avatar_split_clause,[],[f5164,f1491,f1495,f3026])).

fof(f3026,plain,
    ( spl6_173
  <=> r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_173])])).

fof(f1491,plain,
    ( spl6_82
  <=> k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f5164,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | ~ r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ spl6_82 ),
    inference(forward_demodulation,[],[f5162,f121])).

fof(f5162,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | k7_setfam_1(sK0,sK1) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_82 ),
    inference(trivial_inequality_removal,[],[f5150])).

fof(f5150,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | k7_setfam_1(sK0,sK1) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_82 ),
    inference(superposition,[],[f128,f1493])).

fof(f1493,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ spl6_82 ),
    inference(avatar_component_clause,[],[f1491])).

fof(f128,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f92,f117])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f5137,plain,
    ( ~ spl6_81
    | spl6_82
    | ~ spl6_130
    | ~ spl6_248
    | ~ spl6_260 ),
    inference(avatar_split_clause,[],[f5136,f4772,f4608,f2760,f1491,f1487])).

fof(f1487,plain,
    ( spl6_81
  <=> m1_subset_1(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f2760,plain,
    ( spl6_130
  <=> k1_xboole_0 = sK2(k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).

fof(f4608,plain,
    ( spl6_248
  <=> r2_hidden(k3_subset_1(sK0,sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_248])])).

fof(f4772,plain,
    ( spl6_260
  <=> sK2(k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_260])])).

fof(f5136,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ m1_subset_1(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_130
    | ~ spl6_248
    | ~ spl6_260 ),
    inference(forward_demodulation,[],[f5124,f4904])).

fof(f4904,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK0)
    | ~ spl6_130
    | ~ spl6_260 ),
    inference(forward_demodulation,[],[f4774,f2762])).

fof(f2762,plain,
    ( k1_xboole_0 = sK2(k7_setfam_1(sK0,sK1))
    | ~ spl6_130 ),
    inference(avatar_component_clause,[],[f2760])).

fof(f4774,plain,
    ( sK2(k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,sK0)
    | ~ spl6_260 ),
    inference(avatar_component_clause,[],[f4772])).

fof(f5124,plain,
    ( sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,sK0)
    | ~ m1_subset_1(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_248 ),
    inference(superposition,[],[f76,f4924])).

fof(f4924,plain,
    ( sK0 = k3_subset_1(sK0,sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)))
    | ~ spl6_248 ),
    inference(resolution,[],[f4610,f255])).

fof(f255,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = X0 ) ),
    inference(superposition,[],[f140,f120])).

fof(f120,plain,(
    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f59,f117])).

fof(f59,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f140,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f90,f117])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f4610,plain,
    ( r2_hidden(k3_subset_1(sK0,sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))),sK1)
    | ~ spl6_248 ),
    inference(avatar_component_clause,[],[f4608])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f4779,plain,
    ( ~ spl6_73
    | spl6_259 ),
    inference(avatar_contradiction_clause,[],[f4776])).

fof(f4776,plain,
    ( $false
    | ~ spl6_73
    | spl6_259 ),
    inference(subsumption_resolution,[],[f1456,f4769])).

fof(f4769,plain,
    ( ~ r1_tarski(sK2(k7_setfam_1(sK0,sK1)),sK0)
    | spl6_259 ),
    inference(avatar_component_clause,[],[f4767])).

fof(f4767,plain,
    ( spl6_259
  <=> r1_tarski(sK2(k7_setfam_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_259])])).

fof(f1456,plain,
    ( r1_tarski(sK2(k7_setfam_1(sK0,sK1)),sK0)
    | ~ spl6_73 ),
    inference(resolution,[],[f1417,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1417,plain,
    ( m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f1415])).

fof(f1415,plain,
    ( spl6_73
  <=> m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f4775,plain,
    ( ~ spl6_73
    | spl6_260
    | ~ spl6_246 ),
    inference(avatar_split_clause,[],[f4759,f4598,f4772,f1415])).

fof(f4598,plain,
    ( spl6_246
  <=> r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_246])])).

fof(f4759,plain,
    ( sK2(k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,sK0)
    | ~ m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_246 ),
    inference(superposition,[],[f76,f4745])).

fof(f4745,plain,
    ( sK0 = k3_subset_1(sK0,sK2(k7_setfam_1(sK0,sK1)))
    | ~ spl6_246 ),
    inference(resolution,[],[f4600,f255])).

fof(f4600,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,sK1))),sK1)
    | ~ spl6_246 ),
    inference(avatar_component_clause,[],[f4598])).

fof(f4770,plain,
    ( ~ spl6_73
    | spl6_130
    | ~ spl6_259
    | ~ spl6_246 ),
    inference(avatar_split_clause,[],[f4758,f4598,f4767,f2760,f1415])).

fof(f4758,plain,
    ( ~ r1_tarski(sK2(k7_setfam_1(sK0,sK1)),sK0)
    | k1_xboole_0 = sK2(k7_setfam_1(sK0,sK1))
    | ~ m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl6_246 ),
    inference(superposition,[],[f126,f4745])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f78,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f4720,plain,
    ( spl6_173
    | ~ spl6_123
    | ~ spl6_124 ),
    inference(avatar_split_clause,[],[f4713,f2394,f2390,f3026])).

fof(f2390,plain,
    ( spl6_123
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f2394,plain,
    ( spl6_124
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f4713,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1)) ),
    inference(superposition,[],[f2105,f122])).

fof(f122,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f63,f118])).

fof(f118,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f67,f62])).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f2105,plain,(
    ! [X22] :
      ( ~ r2_hidden(k3_subset_1(sK0,X22),sK1)
      | ~ m1_subset_1(X22,k1_zfmisc_1(sK0))
      | r2_hidden(X22,k7_setfam_1(sK0,sK1)) ) ),
    inference(resolution,[],[f694,f58])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f694,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(k3_subset_1(X1,X2),X0)
      | r2_hidden(X2,k7_setfam_1(X1,X0)) ) ),
    inference(duplicate_literal_removal,[],[f689])).

fof(f689,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(k3_subset_1(X1,X2),X0)
      | r2_hidden(X2,k7_setfam_1(X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f139,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f139,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f4611,plain,
    ( spl6_82
    | spl6_83
    | ~ spl6_81
    | spl6_248 ),
    inference(avatar_split_clause,[],[f4578,f4608,f1487,f1495,f1491])).

fof(f4578,plain,
    ( r2_hidden(k3_subset_1(sK0,sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))),sK1)
    | ~ m1_subset_1(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f2053,f441])).

fof(f441,plain,(
    ! [X1] :
      ( r2_hidden(sK4(k1_xboole_0,X1),X1)
      | k1_zfmisc_1(k1_xboole_0) = X1
      | k1_xboole_0 = sK4(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f129,f121])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f91,f117])).

fof(f91,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2053,plain,(
    ! [X22] :
      ( ~ r2_hidden(X22,k7_setfam_1(sK0,sK1))
      | r2_hidden(k3_subset_1(sK0,X22),sK1)
      | ~ m1_subset_1(X22,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f654,f58])).

fof(f654,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | r2_hidden(k3_subset_1(X1,X2),X0)
      | ~ r2_hidden(X2,k7_setfam_1(X1,X0)) ) ),
    inference(duplicate_literal_removal,[],[f649])).

fof(f649,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | r2_hidden(k3_subset_1(X1,X2),X0)
      | ~ r2_hidden(X2,k7_setfam_1(X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f138,f80])).

fof(f138,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f4601,plain,
    ( spl6_72
    | ~ spl6_73
    | spl6_246 ),
    inference(avatar_split_clause,[],[f4576,f4598,f1415,f1411])).

fof(f1411,plain,
    ( spl6_72
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f4576,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,sK1))),sK1)
    | ~ m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f2053,f68])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f2427,plain,(
    spl6_124 ),
    inference(avatar_contradiction_clause,[],[f2426])).

fof(f2426,plain,
    ( $false
    | spl6_124 ),
    inference(subsumption_resolution,[],[f207,f2396])).

fof(f2396,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl6_124 ),
    inference(avatar_component_clause,[],[f2394])).

fof(f207,plain,(
    r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f142,f120])).

fof(f142,plain,(
    ! [X2] : r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f89,f117])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2425,plain,(
    spl6_123 ),
    inference(avatar_contradiction_clause,[],[f2418])).

fof(f2418,plain,
    ( $false
    | spl6_123 ),
    inference(unit_resulting_resolution,[],[f149,f2392,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2392,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl6_123 ),
    inference(avatar_component_clause,[],[f2390])).

fof(f149,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f101,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1498,plain,
    ( spl6_81
    | spl6_82
    | spl6_83 ),
    inference(avatar_split_clause,[],[f1476,f1495,f1491,f1487])).

fof(f1476,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1)
    | k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | m1_subset_1(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f441,f1320])).

fof(f1320,plain,(
    ! [X22] :
      ( ~ r2_hidden(X22,k7_setfam_1(sK0,sK1))
      | m1_subset_1(X22,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f222,f58])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ r2_hidden(X2,k7_setfam_1(X1,X0))
      | m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f80,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f1454,plain,(
    ~ spl6_72 ),
    inference(avatar_contradiction_clause,[],[f1440])).

fof(f1440,plain,
    ( $false
    | ~ spl6_72 ),
    inference(unit_resulting_resolution,[],[f896,f58,f1413,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f1413,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f1411])).

fof(f896,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f876,f120])).

fof(f876,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f875,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f875,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f147,f123])).

fof(f123,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f115])).

fof(f115,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f114])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f69,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f147,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f103,f117,f116,f117,f117])).

fof(f116,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f72,f115])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f1418,plain,
    ( spl6_72
    | spl6_73 ),
    inference(avatar_split_clause,[],[f1406,f1415,f1411])).

fof(f1406,plain,
    ( m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f1320,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:57:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (1010)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (1048)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (1038)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (1013)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (1008)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (1044)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (1040)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (1050)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (1033)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (1007)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (1012)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (1037)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (1009)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.54  % (1017)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.54  % (1032)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.55  % (1046)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.55  % (1019)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.55  % (1021)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.55  % (1047)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (1043)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.39/0.55  % (1029)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.55  % (1018)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.55  % (1020)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.56  % (1034)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.56  % (1011)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.39/0.56  % (1027)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.53/0.56  % (1045)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.53/0.56  % (1035)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.53/0.57  % (1039)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.53/0.57  % (1034)Refutation not found, incomplete strategy% (1034)------------------------------
% 1.53/0.57  % (1034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (1034)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (1034)Memory used [KB]: 10746
% 1.53/0.57  % (1034)Time elapsed: 0.158 s
% 1.53/0.57  % (1034)------------------------------
% 1.53/0.57  % (1034)------------------------------
% 1.53/0.58  % (1049)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 3.13/0.82  % (1076)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.13/0.83  % (1045)Time limit reached!
% 3.13/0.83  % (1045)------------------------------
% 3.13/0.83  % (1045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.83  % (1045)Termination reason: Time limit
% 3.13/0.83  
% 3.13/0.83  % (1045)Memory used [KB]: 11641
% 3.13/0.83  % (1045)Time elapsed: 0.416 s
% 3.13/0.83  % (1045)------------------------------
% 3.13/0.83  % (1045)------------------------------
% 3.60/0.84  % (1009)Time limit reached!
% 3.60/0.84  % (1009)------------------------------
% 3.60/0.84  % (1009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.84  % (1009)Termination reason: Time limit
% 3.60/0.84  
% 3.60/0.84  % (1009)Memory used [KB]: 6396
% 3.60/0.84  % (1009)Time elapsed: 0.426 s
% 3.60/0.84  % (1009)------------------------------
% 3.60/0.84  % (1009)------------------------------
% 3.77/0.91  % (1050)Time limit reached!
% 3.77/0.91  % (1050)------------------------------
% 3.77/0.91  % (1050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.91  % (1050)Termination reason: Time limit
% 3.77/0.91  % (1050)Termination phase: Saturation
% 3.77/0.91  
% 3.77/0.91  % (1050)Memory used [KB]: 2558
% 3.77/0.91  % (1050)Time elapsed: 0.500 s
% 3.77/0.91  % (1050)------------------------------
% 3.77/0.91  % (1050)------------------------------
% 4.28/0.94  % (1032)Time limit reached!
% 4.28/0.94  % (1032)------------------------------
% 4.28/0.94  % (1032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.94  % (1032)Termination reason: Time limit
% 4.28/0.94  
% 4.28/0.94  % (1032)Memory used [KB]: 3709
% 4.28/0.94  % (1032)Time elapsed: 0.529 s
% 4.28/0.94  % (1032)------------------------------
% 4.28/0.94  % (1032)------------------------------
% 4.28/0.95  % (1013)Time limit reached!
% 4.28/0.95  % (1013)------------------------------
% 4.28/0.95  % (1013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.95  % (1013)Termination reason: Time limit
% 4.28/0.95  
% 4.28/0.95  % (1013)Memory used [KB]: 12920
% 4.28/0.95  % (1013)Time elapsed: 0.537 s
% 4.28/0.95  % (1013)------------------------------
% 4.28/0.95  % (1013)------------------------------
% 5.10/1.05  % (1029)Refutation found. Thanks to Tanya!
% 5.10/1.05  % SZS status Theorem for theBenchmark
% 5.10/1.05  % SZS output start Proof for theBenchmark
% 5.10/1.05  fof(f5249,plain,(
% 5.10/1.05    $false),
% 5.10/1.05    inference(avatar_sat_refutation,[],[f1418,f1454,f1498,f2425,f2427,f4601,f4611,f4720,f4770,f4775,f4779,f5137,f5165,f5227])).
% 5.10/1.05  fof(f5227,plain,(
% 5.10/1.05    ~spl6_83),
% 5.10/1.05    inference(avatar_contradiction_clause,[],[f5166])).
% 5.10/1.05  fof(f5166,plain,(
% 5.10/1.05    $false | ~spl6_83),
% 5.10/1.05    inference(subsumption_resolution,[],[f247,f1497])).
% 5.10/1.05  fof(f1497,plain,(
% 5.10/1.05    k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1) | ~spl6_83),
% 5.10/1.05    inference(avatar_component_clause,[],[f1495])).
% 5.10/1.05  fof(f1495,plain,(
% 5.10/1.05    spl6_83 <=> k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1)),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 5.10/1.05  fof(f247,plain,(
% 5.10/1.05    k1_zfmisc_1(k1_xboole_0) != k7_setfam_1(sK0,sK1)),
% 5.10/1.05    inference(forward_demodulation,[],[f119,f121])).
% 5.10/1.05  fof(f121,plain,(
% 5.10/1.05    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 5.10/1.05    inference(definition_unfolding,[],[f61,f117])).
% 5.10/1.05  fof(f117,plain,(
% 5.10/1.05    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 5.10/1.05    inference(definition_unfolding,[],[f66,f114])).
% 5.10/1.05  fof(f114,plain,(
% 5.10/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 5.10/1.05    inference(definition_unfolding,[],[f71,f113])).
% 5.10/1.05  fof(f113,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 5.10/1.05    inference(definition_unfolding,[],[f104,f112])).
% 5.10/1.05  fof(f112,plain,(
% 5.10/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 5.10/1.05    inference(definition_unfolding,[],[f106,f111])).
% 5.10/1.05  fof(f111,plain,(
% 5.10/1.05    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 5.10/1.05    inference(definition_unfolding,[],[f107,f110])).
% 5.10/1.05  fof(f110,plain,(
% 5.10/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 5.10/1.05    inference(definition_unfolding,[],[f108,f109])).
% 5.10/1.05  fof(f109,plain,(
% 5.10/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f12])).
% 5.10/1.05  fof(f12,axiom,(
% 5.10/1.05    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 5.10/1.05  fof(f108,plain,(
% 5.10/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f11])).
% 5.10/1.05  fof(f11,axiom,(
% 5.10/1.05    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 5.10/1.05  fof(f107,plain,(
% 5.10/1.05    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f10])).
% 5.10/1.05  fof(f10,axiom,(
% 5.10/1.05    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 5.10/1.05  fof(f106,plain,(
% 5.10/1.05    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f9])).
% 5.10/1.05  fof(f9,axiom,(
% 5.10/1.05    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 5.10/1.05  fof(f104,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f8])).
% 5.10/1.05  fof(f8,axiom,(
% 5.10/1.05    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 5.10/1.05  fof(f71,plain,(
% 5.10/1.05    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f7])).
% 5.10/1.05  fof(f7,axiom,(
% 5.10/1.05    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 5.10/1.05  fof(f66,plain,(
% 5.10/1.05    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f6])).
% 5.10/1.05  fof(f6,axiom,(
% 5.10/1.05    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 5.10/1.05  fof(f61,plain,(
% 5.10/1.05    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 5.10/1.05    inference(cnf_transformation,[],[f14])).
% 5.10/1.05  fof(f14,axiom,(
% 5.10/1.05    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 5.10/1.05  fof(f119,plain,(
% 5.10/1.05    k7_setfam_1(sK0,sK1) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 5.10/1.05    inference(definition_unfolding,[],[f60,f117])).
% 5.10/1.05  fof(f60,plain,(
% 5.10/1.05    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1)),
% 5.10/1.05    inference(cnf_transformation,[],[f39])).
% 5.10/1.05  fof(f39,plain,(
% 5.10/1.05    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.10/1.05    inference(flattening,[],[f38])).
% 5.10/1.05  fof(f38,plain,(
% 5.10/1.05    ? [X0,X1] : ((k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.10/1.05    inference(ennf_transformation,[],[f36])).
% 5.10/1.05  fof(f36,negated_conjecture,(
% 5.10/1.05    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 5.10/1.05    inference(negated_conjecture,[],[f35])).
% 5.10/1.05  fof(f35,conjecture,(
% 5.10/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).
% 5.10/1.05  fof(f5165,plain,(
% 5.10/1.05    ~spl6_173 | spl6_83 | ~spl6_82),
% 5.10/1.05    inference(avatar_split_clause,[],[f5164,f1491,f1495,f3026])).
% 5.10/1.05  fof(f3026,plain,(
% 5.10/1.05    spl6_173 <=> r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_173])])).
% 5.10/1.05  fof(f1491,plain,(
% 5.10/1.05    spl6_82 <=> k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).
% 5.10/1.05  fof(f5164,plain,(
% 5.10/1.05    k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1) | ~r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1)) | ~spl6_82),
% 5.10/1.05    inference(forward_demodulation,[],[f5162,f121])).
% 5.10/1.05  fof(f5162,plain,(
% 5.10/1.05    ~r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1)) | k7_setfam_1(sK0,sK1) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_82),
% 5.10/1.05    inference(trivial_inequality_removal,[],[f5150])).
% 5.10/1.05  fof(f5150,plain,(
% 5.10/1.05    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1)) | k7_setfam_1(sK0,sK1) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_82),
% 5.10/1.05    inference(superposition,[],[f128,f1493])).
% 5.10/1.05  fof(f1493,plain,(
% 5.10/1.05    k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)) | ~spl6_82),
% 5.10/1.05    inference(avatar_component_clause,[],[f1491])).
% 5.10/1.05  fof(f128,plain,(
% 5.10/1.05    ( ! [X0,X1] : (sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1) )),
% 5.10/1.05    inference(definition_unfolding,[],[f92,f117])).
% 5.10/1.05  fof(f92,plain,(
% 5.10/1.05    ( ! [X0,X1] : (sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 5.10/1.05    inference(cnf_transformation,[],[f5])).
% 5.10/1.05  fof(f5,axiom,(
% 5.10/1.05    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 5.10/1.05  fof(f5137,plain,(
% 5.10/1.05    ~spl6_81 | spl6_82 | ~spl6_130 | ~spl6_248 | ~spl6_260),
% 5.10/1.05    inference(avatar_split_clause,[],[f5136,f4772,f4608,f2760,f1491,f1487])).
% 5.10/1.05  fof(f1487,plain,(
% 5.10/1.05    spl6_81 <=> m1_subset_1(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 5.10/1.05  fof(f2760,plain,(
% 5.10/1.05    spl6_130 <=> k1_xboole_0 = sK2(k7_setfam_1(sK0,sK1))),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).
% 5.10/1.05  fof(f4608,plain,(
% 5.10/1.05    spl6_248 <=> r2_hidden(k3_subset_1(sK0,sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))),sK1)),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_248])])).
% 5.10/1.05  fof(f4772,plain,(
% 5.10/1.05    spl6_260 <=> sK2(k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,sK0)),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_260])])).
% 5.10/1.05  fof(f5136,plain,(
% 5.10/1.05    k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)) | ~m1_subset_1(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | (~spl6_130 | ~spl6_248 | ~spl6_260)),
% 5.10/1.05    inference(forward_demodulation,[],[f5124,f4904])).
% 5.10/1.05  fof(f4904,plain,(
% 5.10/1.05    k1_xboole_0 = k3_subset_1(sK0,sK0) | (~spl6_130 | ~spl6_260)),
% 5.10/1.05    inference(forward_demodulation,[],[f4774,f2762])).
% 5.10/1.05  fof(f2762,plain,(
% 5.10/1.05    k1_xboole_0 = sK2(k7_setfam_1(sK0,sK1)) | ~spl6_130),
% 5.10/1.05    inference(avatar_component_clause,[],[f2760])).
% 5.10/1.05  fof(f4774,plain,(
% 5.10/1.05    sK2(k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,sK0) | ~spl6_260),
% 5.10/1.05    inference(avatar_component_clause,[],[f4772])).
% 5.10/1.05  fof(f5124,plain,(
% 5.10/1.05    sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,sK0) | ~m1_subset_1(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl6_248),
% 5.10/1.05    inference(superposition,[],[f76,f4924])).
% 5.10/1.05  fof(f4924,plain,(
% 5.10/1.05    sK0 = k3_subset_1(sK0,sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))) | ~spl6_248),
% 5.10/1.05    inference(resolution,[],[f4610,f255])).
% 5.10/1.05  fof(f255,plain,(
% 5.10/1.05    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) )),
% 5.10/1.05    inference(superposition,[],[f140,f120])).
% 5.10/1.05  fof(f120,plain,(
% 5.10/1.05    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 5.10/1.05    inference(definition_unfolding,[],[f59,f117])).
% 5.10/1.05  fof(f59,plain,(
% 5.10/1.05    sK1 = k1_tarski(sK0)),
% 5.10/1.05    inference(cnf_transformation,[],[f39])).
% 5.10/1.05  fof(f140,plain,(
% 5.10/1.05    ( ! [X2,X0] : (~r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X2) )),
% 5.10/1.05    inference(equality_resolution,[],[f130])).
% 5.10/1.05  fof(f130,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 5.10/1.05    inference(definition_unfolding,[],[f90,f117])).
% 5.10/1.05  fof(f90,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 5.10/1.05    inference(cnf_transformation,[],[f5])).
% 5.10/1.05  fof(f4610,plain,(
% 5.10/1.05    r2_hidden(k3_subset_1(sK0,sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))),sK1) | ~spl6_248),
% 5.10/1.05    inference(avatar_component_clause,[],[f4608])).
% 5.10/1.05  fof(f76,plain,(
% 5.10/1.05    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.10/1.05    inference(cnf_transformation,[],[f45])).
% 5.10/1.05  fof(f45,plain,(
% 5.10/1.05    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.10/1.05    inference(ennf_transformation,[],[f19])).
% 5.10/1.05  fof(f19,axiom,(
% 5.10/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 5.10/1.05  fof(f4779,plain,(
% 5.10/1.05    ~spl6_73 | spl6_259),
% 5.10/1.05    inference(avatar_contradiction_clause,[],[f4776])).
% 5.10/1.05  fof(f4776,plain,(
% 5.10/1.05    $false | (~spl6_73 | spl6_259)),
% 5.10/1.05    inference(subsumption_resolution,[],[f1456,f4769])).
% 5.10/1.05  fof(f4769,plain,(
% 5.10/1.05    ~r1_tarski(sK2(k7_setfam_1(sK0,sK1)),sK0) | spl6_259),
% 5.10/1.05    inference(avatar_component_clause,[],[f4767])).
% 5.10/1.05  fof(f4767,plain,(
% 5.10/1.05    spl6_259 <=> r1_tarski(sK2(k7_setfam_1(sK0,sK1)),sK0)),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_259])])).
% 5.10/1.05  fof(f1456,plain,(
% 5.10/1.05    r1_tarski(sK2(k7_setfam_1(sK0,sK1)),sK0) | ~spl6_73),
% 5.10/1.05    inference(resolution,[],[f1417,f101])).
% 5.10/1.05  fof(f101,plain,(
% 5.10/1.05    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f30])).
% 5.10/1.05  fof(f30,axiom,(
% 5.10/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 5.10/1.05  fof(f1417,plain,(
% 5.10/1.05    m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl6_73),
% 5.10/1.05    inference(avatar_component_clause,[],[f1415])).
% 5.10/1.05  fof(f1415,plain,(
% 5.10/1.05    spl6_73 <=> m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 5.10/1.05  fof(f4775,plain,(
% 5.10/1.05    ~spl6_73 | spl6_260 | ~spl6_246),
% 5.10/1.05    inference(avatar_split_clause,[],[f4759,f4598,f4772,f1415])).
% 5.10/1.05  fof(f4598,plain,(
% 5.10/1.05    spl6_246 <=> r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,sK1))),sK1)),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_246])])).
% 5.10/1.05  fof(f4759,plain,(
% 5.10/1.05    sK2(k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,sK0) | ~m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl6_246),
% 5.10/1.05    inference(superposition,[],[f76,f4745])).
% 5.10/1.05  fof(f4745,plain,(
% 5.10/1.05    sK0 = k3_subset_1(sK0,sK2(k7_setfam_1(sK0,sK1))) | ~spl6_246),
% 5.10/1.05    inference(resolution,[],[f4600,f255])).
% 5.10/1.05  fof(f4600,plain,(
% 5.10/1.05    r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,sK1))),sK1) | ~spl6_246),
% 5.10/1.05    inference(avatar_component_clause,[],[f4598])).
% 5.10/1.05  fof(f4770,plain,(
% 5.10/1.05    ~spl6_73 | spl6_130 | ~spl6_259 | ~spl6_246),
% 5.10/1.05    inference(avatar_split_clause,[],[f4758,f4598,f4767,f2760,f1415])).
% 5.10/1.05  fof(f4758,plain,(
% 5.10/1.05    ~r1_tarski(sK2(k7_setfam_1(sK0,sK1)),sK0) | k1_xboole_0 = sK2(k7_setfam_1(sK0,sK1)) | ~m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl6_246),
% 5.10/1.05    inference(superposition,[],[f126,f4745])).
% 5.10/1.05  fof(f126,plain,(
% 5.10/1.05    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.10/1.05    inference(definition_unfolding,[],[f78,f62])).
% 5.10/1.05  fof(f62,plain,(
% 5.10/1.05    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f17])).
% 5.10/1.05  fof(f17,axiom,(
% 5.10/1.05    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 5.10/1.05  fof(f78,plain,(
% 5.10/1.05    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 5.10/1.05    inference(cnf_transformation,[],[f46])).
% 5.10/1.05  fof(f46,plain,(
% 5.10/1.05    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.10/1.05    inference(ennf_transformation,[],[f21])).
% 5.10/1.05  fof(f21,axiom,(
% 5.10/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 5.10/1.05  fof(f4720,plain,(
% 5.10/1.05    spl6_173 | ~spl6_123 | ~spl6_124),
% 5.10/1.05    inference(avatar_split_clause,[],[f4713,f2394,f2390,f3026])).
% 5.10/1.05  fof(f2390,plain,(
% 5.10/1.05    spl6_123 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).
% 5.10/1.05  fof(f2394,plain,(
% 5.10/1.05    spl6_124 <=> r2_hidden(sK0,sK1)),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).
% 5.10/1.05  fof(f4713,plain,(
% 5.10/1.05    ~r2_hidden(sK0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))),
% 5.10/1.05    inference(superposition,[],[f2105,f122])).
% 5.10/1.05  fof(f122,plain,(
% 5.10/1.05    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 5.10/1.05    inference(definition_unfolding,[],[f63,f118])).
% 5.10/1.05  fof(f118,plain,(
% 5.10/1.05    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 5.10/1.05    inference(definition_unfolding,[],[f67,f62])).
% 5.10/1.05  fof(f67,plain,(
% 5.10/1.05    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 5.10/1.05    inference(cnf_transformation,[],[f20])).
% 5.10/1.05  fof(f20,axiom,(
% 5.10/1.05    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 5.10/1.05  fof(f63,plain,(
% 5.10/1.05    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 5.10/1.05    inference(cnf_transformation,[],[f18])).
% 5.10/1.05  fof(f18,axiom,(
% 5.10/1.05    ! [X0] : k2_subset_1(X0) = X0),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 5.10/1.05  fof(f2105,plain,(
% 5.10/1.05    ( ! [X22] : (~r2_hidden(k3_subset_1(sK0,X22),sK1) | ~m1_subset_1(X22,k1_zfmisc_1(sK0)) | r2_hidden(X22,k7_setfam_1(sK0,sK1))) )),
% 5.10/1.05    inference(resolution,[],[f694,f58])).
% 5.10/1.05  fof(f58,plain,(
% 5.10/1.05    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 5.10/1.05    inference(cnf_transformation,[],[f39])).
% 5.10/1.05  fof(f694,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r2_hidden(k3_subset_1(X1,X2),X0) | r2_hidden(X2,k7_setfam_1(X1,X0))) )),
% 5.10/1.05    inference(duplicate_literal_removal,[],[f689])).
% 5.10/1.05  fof(f689,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r2_hidden(k3_subset_1(X1,X2),X0) | r2_hidden(X2,k7_setfam_1(X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))) )),
% 5.10/1.05    inference(resolution,[],[f139,f80])).
% 5.10/1.05  fof(f80,plain,(
% 5.10/1.05    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 5.10/1.05    inference(cnf_transformation,[],[f48])).
% 5.10/1.05  fof(f48,plain,(
% 5.10/1.05    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.10/1.05    inference(ennf_transformation,[],[f26])).
% 5.10/1.05  fof(f26,axiom,(
% 5.10/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 5.10/1.05  fof(f139,plain,(
% 5.10/1.05    ( ! [X0,X3,X1] : (~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,k7_setfam_1(X0,X1))) )),
% 5.10/1.05    inference(equality_resolution,[],[f86])).
% 5.10/1.05  fof(f86,plain,(
% 5.10/1.05    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2) | k7_setfam_1(X0,X1) != X2) )),
% 5.10/1.05    inference(cnf_transformation,[],[f55])).
% 5.10/1.05  fof(f55,plain,(
% 5.10/1.05    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.10/1.05    inference(ennf_transformation,[],[f25])).
% 5.10/1.05  fof(f25,axiom,(
% 5.10/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).
% 5.10/1.05  fof(f4611,plain,(
% 5.10/1.05    spl6_82 | spl6_83 | ~spl6_81 | spl6_248),
% 5.10/1.05    inference(avatar_split_clause,[],[f4578,f4608,f1487,f1495,f1491])).
% 5.10/1.05  fof(f4578,plain,(
% 5.10/1.05    r2_hidden(k3_subset_1(sK0,sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))),sK1) | ~m1_subset_1(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1) | k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1))),
% 5.10/1.05    inference(resolution,[],[f2053,f441])).
% 5.10/1.05  fof(f441,plain,(
% 5.10/1.05    ( ! [X1] : (r2_hidden(sK4(k1_xboole_0,X1),X1) | k1_zfmisc_1(k1_xboole_0) = X1 | k1_xboole_0 = sK4(k1_xboole_0,X1)) )),
% 5.10/1.05    inference(superposition,[],[f129,f121])).
% 5.10/1.05  fof(f129,plain,(
% 5.10/1.05    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) = X0) )),
% 5.10/1.05    inference(definition_unfolding,[],[f91,f117])).
% 5.10/1.05  fof(f91,plain,(
% 5.10/1.05    ( ! [X0,X1] : (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 5.10/1.05    inference(cnf_transformation,[],[f5])).
% 5.10/1.05  fof(f2053,plain,(
% 5.10/1.05    ( ! [X22] : (~r2_hidden(X22,k7_setfam_1(sK0,sK1)) | r2_hidden(k3_subset_1(sK0,X22),sK1) | ~m1_subset_1(X22,k1_zfmisc_1(sK0))) )),
% 5.10/1.05    inference(resolution,[],[f654,f58])).
% 5.10/1.05  fof(f654,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r2_hidden(k3_subset_1(X1,X2),X0) | ~r2_hidden(X2,k7_setfam_1(X1,X0))) )),
% 5.10/1.05    inference(duplicate_literal_removal,[],[f649])).
% 5.10/1.05  fof(f649,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r2_hidden(k3_subset_1(X1,X2),X0) | ~r2_hidden(X2,k7_setfam_1(X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))) )),
% 5.10/1.05    inference(resolution,[],[f138,f80])).
% 5.10/1.05  fof(f138,plain,(
% 5.10/1.05    ( ! [X0,X3,X1] : (~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,k7_setfam_1(X0,X1))) )),
% 5.10/1.05    inference(equality_resolution,[],[f87])).
% 5.10/1.05  fof(f87,plain,(
% 5.10/1.05    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2) | k7_setfam_1(X0,X1) != X2) )),
% 5.10/1.05    inference(cnf_transformation,[],[f55])).
% 5.10/1.05  fof(f4601,plain,(
% 5.10/1.05    spl6_72 | ~spl6_73 | spl6_246),
% 5.10/1.05    inference(avatar_split_clause,[],[f4576,f4598,f1415,f1411])).
% 5.10/1.05  fof(f1411,plain,(
% 5.10/1.05    spl6_72 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 5.10/1.05    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 5.10/1.05  fof(f4576,plain,(
% 5.10/1.05    r2_hidden(k3_subset_1(sK0,sK2(k7_setfam_1(sK0,sK1))),sK1) | ~m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 5.10/1.05    inference(resolution,[],[f2053,f68])).
% 5.10/1.05  fof(f68,plain,(
% 5.10/1.05    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 5.10/1.05    inference(cnf_transformation,[],[f40])).
% 5.10/1.05  fof(f40,plain,(
% 5.10/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 5.10/1.05    inference(ennf_transformation,[],[f2])).
% 5.10/1.05  fof(f2,axiom,(
% 5.10/1.05    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 5.10/1.05  fof(f2427,plain,(
% 5.10/1.05    spl6_124),
% 5.10/1.05    inference(avatar_contradiction_clause,[],[f2426])).
% 5.10/1.05  fof(f2426,plain,(
% 5.10/1.05    $false | spl6_124),
% 5.10/1.05    inference(subsumption_resolution,[],[f207,f2396])).
% 5.10/1.05  fof(f2396,plain,(
% 5.10/1.05    ~r2_hidden(sK0,sK1) | spl6_124),
% 5.10/1.05    inference(avatar_component_clause,[],[f2394])).
% 5.10/1.05  fof(f207,plain,(
% 5.10/1.05    r2_hidden(sK0,sK1)),
% 5.10/1.05    inference(superposition,[],[f142,f120])).
% 5.10/1.05  fof(f142,plain,(
% 5.10/1.05    ( ! [X2] : (r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 5.10/1.05    inference(equality_resolution,[],[f141])).
% 5.10/1.05  fof(f141,plain,(
% 5.10/1.05    ( ! [X2,X1] : (r2_hidden(X2,X1) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1) )),
% 5.10/1.05    inference(equality_resolution,[],[f131])).
% 5.10/1.05  fof(f131,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 5.10/1.05    inference(definition_unfolding,[],[f89,f117])).
% 5.10/1.05  fof(f89,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 5.10/1.05    inference(cnf_transformation,[],[f5])).
% 5.10/1.05  fof(f2425,plain,(
% 5.10/1.05    spl6_123),
% 5.10/1.05    inference(avatar_contradiction_clause,[],[f2418])).
% 5.10/1.05  fof(f2418,plain,(
% 5.10/1.05    $false | spl6_123),
% 5.10/1.05    inference(unit_resulting_resolution,[],[f149,f2392,f100])).
% 5.10/1.05  fof(f100,plain,(
% 5.10/1.05    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f30])).
% 5.10/1.05  fof(f2392,plain,(
% 5.10/1.05    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | spl6_123),
% 5.10/1.05    inference(avatar_component_clause,[],[f2390])).
% 5.10/1.05  fof(f149,plain,(
% 5.10/1.05    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 5.10/1.05    inference(resolution,[],[f101,f64])).
% 5.10/1.05  fof(f64,plain,(
% 5.10/1.05    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 5.10/1.05    inference(cnf_transformation,[],[f22])).
% 5.10/1.05  fof(f22,axiom,(
% 5.10/1.05    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 5.10/1.05  fof(f1498,plain,(
% 5.10/1.05    spl6_81 | spl6_82 | spl6_83),
% 5.10/1.05    inference(avatar_split_clause,[],[f1476,f1495,f1491,f1487])).
% 5.10/1.05  fof(f1476,plain,(
% 5.10/1.05    k1_zfmisc_1(k1_xboole_0) = k7_setfam_1(sK0,sK1) | k1_xboole_0 = sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)) | m1_subset_1(sK4(k1_xboole_0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))),
% 5.10/1.05    inference(resolution,[],[f441,f1320])).
% 5.10/1.05  fof(f1320,plain,(
% 5.10/1.05    ( ! [X22] : (~r2_hidden(X22,k7_setfam_1(sK0,sK1)) | m1_subset_1(X22,k1_zfmisc_1(sK0))) )),
% 5.10/1.05    inference(resolution,[],[f222,f58])).
% 5.10/1.05  fof(f222,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~r2_hidden(X2,k7_setfam_1(X1,X0)) | m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 5.10/1.05    inference(resolution,[],[f80,f105])).
% 5.10/1.05  fof(f105,plain,(
% 5.10/1.05    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f57])).
% 5.10/1.05  fof(f57,plain,(
% 5.10/1.05    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 5.10/1.05    inference(flattening,[],[f56])).
% 5.10/1.05  fof(f56,plain,(
% 5.10/1.05    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 5.10/1.05    inference(ennf_transformation,[],[f32])).
% 5.10/1.05  fof(f32,axiom,(
% 5.10/1.05    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 5.10/1.05  fof(f1454,plain,(
% 5.10/1.05    ~spl6_72),
% 5.10/1.05    inference(avatar_contradiction_clause,[],[f1440])).
% 5.10/1.05  fof(f1440,plain,(
% 5.10/1.05    $false | ~spl6_72),
% 5.10/1.05    inference(unit_resulting_resolution,[],[f896,f58,f1413,f81])).
% 5.10/1.05  fof(f81,plain,(
% 5.10/1.05    ( ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 5.10/1.05    inference(cnf_transformation,[],[f50])).
% 5.10/1.05  fof(f50,plain,(
% 5.10/1.05    ! [X0,X1] : (k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.10/1.05    inference(flattening,[],[f49])).
% 5.10/1.05  fof(f49,plain,(
% 5.10/1.05    ! [X0,X1] : ((k1_xboole_0 != k7_setfam_1(X0,X1) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.10/1.05    inference(ennf_transformation,[],[f31])).
% 5.10/1.05  fof(f31,axiom,(
% 5.10/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).
% 5.10/1.05  fof(f1413,plain,(
% 5.10/1.05    k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl6_72),
% 5.10/1.05    inference(avatar_component_clause,[],[f1411])).
% 5.10/1.05  fof(f896,plain,(
% 5.10/1.05    k1_xboole_0 != sK1),
% 5.10/1.05    inference(superposition,[],[f876,f120])).
% 5.10/1.05  fof(f876,plain,(
% 5.10/1.05    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 5.10/1.05    inference(forward_demodulation,[],[f875,f65])).
% 5.10/1.05  fof(f65,plain,(
% 5.10/1.05    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.10/1.05    inference(cnf_transformation,[],[f4])).
% 5.10/1.05  fof(f4,axiom,(
% 5.10/1.05    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.10/1.05  fof(f875,plain,(
% 5.10/1.05    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 5.10/1.05    inference(forward_demodulation,[],[f147,f123])).
% 5.10/1.05  fof(f123,plain,(
% 5.10/1.05    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 5.10/1.05    inference(definition_unfolding,[],[f69,f115])).
% 5.10/1.05  fof(f115,plain,(
% 5.10/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 5.10/1.05    inference(definition_unfolding,[],[f70,f114])).
% 5.10/1.05  fof(f70,plain,(
% 5.10/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 5.10/1.05    inference(cnf_transformation,[],[f28])).
% 5.10/1.05  fof(f28,axiom,(
% 5.10/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 5.10/1.05  fof(f69,plain,(
% 5.10/1.05    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.10/1.05    inference(cnf_transformation,[],[f37])).
% 5.10/1.05  fof(f37,plain,(
% 5.10/1.05    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 5.10/1.05    inference(rectify,[],[f1])).
% 5.10/1.05  fof(f1,axiom,(
% 5.10/1.05    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 5.10/1.05  fof(f147,plain,(
% 5.10/1.05    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 5.10/1.05    inference(equality_resolution,[],[f135])).
% 5.10/1.05  fof(f135,plain,(
% 5.10/1.05    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 5.10/1.05    inference(definition_unfolding,[],[f103,f117,f116,f117,f117])).
% 5.10/1.05  fof(f116,plain,(
% 5.10/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 5.10/1.05    inference(definition_unfolding,[],[f72,f115])).
% 5.10/1.05  fof(f72,plain,(
% 5.10/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.10/1.05    inference(cnf_transformation,[],[f3])).
% 5.10/1.05  fof(f3,axiom,(
% 5.10/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.10/1.05  fof(f103,plain,(
% 5.10/1.05    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 5.10/1.05    inference(cnf_transformation,[],[f15])).
% 5.10/1.05  fof(f15,axiom,(
% 5.10/1.05    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 5.10/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 5.10/1.05  fof(f1418,plain,(
% 5.10/1.05    spl6_72 | spl6_73),
% 5.10/1.05    inference(avatar_split_clause,[],[f1406,f1415,f1411])).
% 5.10/1.05  fof(f1406,plain,(
% 5.10/1.05    m1_subset_1(sK2(k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 5.10/1.05    inference(resolution,[],[f1320,f68])).
% 5.10/1.05  % SZS output end Proof for theBenchmark
% 5.10/1.05  % (1029)------------------------------
% 5.10/1.05  % (1029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.10/1.05  % (1029)Termination reason: Refutation
% 5.10/1.05  
% 5.10/1.05  % (1029)Memory used [KB]: 8827
% 5.10/1.05  % (1029)Time elapsed: 0.643 s
% 5.10/1.05  % (1029)------------------------------
% 5.10/1.05  % (1029)------------------------------
% 5.10/1.07  % (1087)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 5.10/1.07  % (1017)Time limit reached!
% 5.10/1.07  % (1017)------------------------------
% 5.10/1.07  % (1017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.10/1.07  % (1017)Termination reason: Time limit
% 5.10/1.07  
% 5.10/1.07  % (1017)Memory used [KB]: 5245
% 5.10/1.07  % (1017)Time elapsed: 0.622 s
% 5.10/1.07  % (1017)------------------------------
% 5.10/1.07  % (1017)------------------------------
% 5.10/1.08  % (1006)Success in time 0.709 s
%------------------------------------------------------------------------------
