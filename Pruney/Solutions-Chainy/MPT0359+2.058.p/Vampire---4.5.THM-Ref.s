%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:46 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 280 expanded)
%              Number of leaves         :   41 ( 109 expanded)
%              Depth                    :   15
%              Number of atoms          :  339 ( 584 expanded)
%              Number of equality atoms :   95 ( 204 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f696,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f109,f114,f182,f260,f272,f418,f509,f534,f540,f590,f593,f620,f672,f685,f694,f695])).

fof(f695,plain,
    ( k3_subset_1(sK0,sK1) != k1_subset_1(sK0)
    | k1_xboole_0 != k1_subset_1(sK0)
    | k1_xboole_0 != k3_subset_1(sK0,sK0)
    | sK0 != k3_subset_1(sK0,k3_subset_1(sK0,sK0))
    | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | sK0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f694,plain,
    ( spl3_39
    | ~ spl3_1
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f689,f268,f257,f100,f691])).

fof(f691,plain,
    ( spl3_39
  <=> k3_subset_1(sK0,sK1) = k1_subset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f100,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f257,plain,
    ( spl3_18
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f268,plain,
    ( spl3_20
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f689,plain,
    ( k3_subset_1(sK0,sK1) = k1_subset_1(sK0)
    | ~ spl3_1
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f688,f259])).

fof(f259,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f257])).

fof(f688,plain,
    ( k3_subset_1(sK0,sK1) = k1_subset_1(sK0)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f686,f101])).

fof(f101,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f686,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) = k1_subset_1(sK0)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_20 ),
    inference(superposition,[],[f70,f270])).

fof(f270,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f268])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f685,plain,
    ( ~ spl3_30
    | spl3_38
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f680,f669,f682,f542])).

fof(f542,plain,
    ( spl3_30
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f682,plain,
    ( spl3_38
  <=> k1_xboole_0 = k1_subset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f669,plain,
    ( spl3_37
  <=> sK0 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f680,plain,
    ( k1_xboole_0 = k1_subset_1(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f677,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f677,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 = k1_subset_1(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl3_37 ),
    inference(superposition,[],[f70,f671])).

fof(f671,plain,
    ( sK0 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f669])).

fof(f672,plain,
    ( spl3_37
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f667,f143,f138,f669])).

fof(f138,plain,
    ( spl3_6
  <=> k1_xboole_0 = k3_subset_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f143,plain,
    ( spl3_7
  <=> sK0 = k3_subset_1(sK0,k3_subset_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f667,plain,
    ( sK0 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f145,f140])).

fof(f140,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f145,plain,
    ( sK0 = k3_subset_1(sK0,k3_subset_1(sK0,sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f620,plain,
    ( spl3_30
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f619,f138,f117,f542])).

fof(f117,plain,
    ( spl3_4
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f619,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f618,f119])).

fof(f119,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f618,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(superposition,[],[f67,f140])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f593,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f592,f117,f138])).

fof(f592,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f591,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f591,plain,
    ( k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f580,f92])).

fof(f92,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f58,f87])).

fof(f87,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f77,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f580,plain,
    ( k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK0),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl3_4 ),
    inference(resolution,[],[f119,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f88])).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f61,f87])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f590,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f579,f117,f143])).

fof(f579,plain,
    ( sK0 = k3_subset_1(sK0,k3_subset_1(sK0,sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f119,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f540,plain,
    ( spl3_4
    | spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f372,f156,f152,f117])).

fof(f152,plain,
    ( spl3_8
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f156,plain,
    ( spl3_9
  <=> r2_hidden(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f372,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_8
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f153,f158,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f158,plain,
    ( r2_hidden(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f156])).

fof(f153,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f534,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f90,f157,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f75,f85])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f157,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f156])).

fof(f90,plain,(
    ! [X0] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f53,f89])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f85])).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f509,plain,
    ( ~ spl3_6
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | ~ spl3_6
    | spl3_12 ),
    inference(subsumption_resolution,[],[f504,f50])).

fof(f504,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl3_6
    | spl3_12 ),
    inference(backward_demodulation,[],[f181,f140])).

fof(f181,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl3_12
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f418,plain,
    ( ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f373,f156,f152])).

fof(f373,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f158,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f272,plain,
    ( spl3_20
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f246,f111,f268])).

fof(f111,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f246,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f113,f69])).

fof(f113,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f260,plain,
    ( spl3_18
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f243,f111,f257])).

fof(f243,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f113,f67])).

fof(f182,plain,
    ( ~ spl3_12
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f177,f104,f100,f179])).

fof(f104,plain,
    ( spl3_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f177,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f102,f105])).

fof(f105,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f102,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f114,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f47,f111])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f109,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f108,f104,f100])).

fof(f108,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f48,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f48,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f98,f104,f100])).

fof(f98,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f49,f51])).

fof(f49,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (22458)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (22455)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (22457)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (22456)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (22454)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (22453)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (22459)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (22473)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (22475)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (22476)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (22453)Refutation not found, incomplete strategy% (22453)------------------------------
% 0.21/0.52  % (22453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22468)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (22470)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (22465)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (22457)Refutation not found, incomplete strategy% (22457)------------------------------
% 0.21/0.53  % (22457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22457)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22457)Memory used [KB]: 6140
% 0.21/0.53  % (22457)Time elapsed: 0.127 s
% 0.21/0.53  % (22457)------------------------------
% 0.21/0.53  % (22457)------------------------------
% 0.21/0.53  % (22461)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (22464)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (22462)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (22481)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (22477)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (22478)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (22462)Refutation not found, incomplete strategy% (22462)------------------------------
% 0.21/0.53  % (22462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22462)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22462)Memory used [KB]: 10618
% 0.21/0.53  % (22462)Time elapsed: 0.129 s
% 0.21/0.53  % (22462)------------------------------
% 0.21/0.53  % (22462)------------------------------
% 0.21/0.53  % (22453)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22453)Memory used [KB]: 1663
% 0.21/0.53  % (22453)Time elapsed: 0.115 s
% 0.21/0.53  % (22453)------------------------------
% 0.21/0.53  % (22453)------------------------------
% 0.21/0.53  % (22460)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (22469)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (22482)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (22470)Refutation not found, incomplete strategy% (22470)------------------------------
% 0.21/0.53  % (22470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22475)Refutation not found, incomplete strategy% (22475)------------------------------
% 0.21/0.53  % (22475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22466)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (22475)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22475)Memory used [KB]: 10746
% 0.21/0.53  % (22475)Time elapsed: 0.133 s
% 0.21/0.53  % (22474)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (22475)------------------------------
% 0.21/0.53  % (22475)------------------------------
% 1.35/0.54  % (22467)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.54  % (22480)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.54  % (22479)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.54  % (22471)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (22472)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.54  % (22470)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (22470)Memory used [KB]: 10618
% 1.35/0.54  % (22470)Time elapsed: 0.127 s
% 1.35/0.54  % (22470)------------------------------
% 1.35/0.54  % (22470)------------------------------
% 1.35/0.55  % (22463)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (22463)Refutation not found, incomplete strategy% (22463)------------------------------
% 1.35/0.55  % (22463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (22463)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (22463)Memory used [KB]: 10618
% 1.49/0.55  % (22463)Time elapsed: 0.138 s
% 1.49/0.55  % (22463)------------------------------
% 1.49/0.55  % (22463)------------------------------
% 1.49/0.56  % (22478)Refutation found. Thanks to Tanya!
% 1.49/0.56  % SZS status Theorem for theBenchmark
% 1.49/0.56  % SZS output start Proof for theBenchmark
% 1.49/0.56  fof(f696,plain,(
% 1.49/0.56    $false),
% 1.49/0.56    inference(avatar_sat_refutation,[],[f107,f109,f114,f182,f260,f272,f418,f509,f534,f540,f590,f593,f620,f672,f685,f694,f695])).
% 1.49/0.56  fof(f695,plain,(
% 1.49/0.56    k3_subset_1(sK0,sK1) != k1_subset_1(sK0) | k1_xboole_0 != k1_subset_1(sK0) | k1_xboole_0 != k3_subset_1(sK0,sK0) | sK0 != k3_subset_1(sK0,k3_subset_1(sK0,sK0)) | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | sK0 = sK1),
% 1.49/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.49/0.56  fof(f694,plain,(
% 1.49/0.56    spl3_39 | ~spl3_1 | ~spl3_18 | ~spl3_20),
% 1.49/0.56    inference(avatar_split_clause,[],[f689,f268,f257,f100,f691])).
% 1.49/0.56  fof(f691,plain,(
% 1.49/0.56    spl3_39 <=> k3_subset_1(sK0,sK1) = k1_subset_1(sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.49/0.56  fof(f100,plain,(
% 1.49/0.56    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.49/0.56  fof(f257,plain,(
% 1.49/0.56    spl3_18 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.49/0.56  fof(f268,plain,(
% 1.49/0.56    spl3_20 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.49/0.56  fof(f689,plain,(
% 1.49/0.56    k3_subset_1(sK0,sK1) = k1_subset_1(sK0) | (~spl3_1 | ~spl3_18 | ~spl3_20)),
% 1.49/0.56    inference(subsumption_resolution,[],[f688,f259])).
% 1.49/0.56  fof(f259,plain,(
% 1.49/0.56    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_18),
% 1.49/0.56    inference(avatar_component_clause,[],[f257])).
% 1.49/0.56  fof(f688,plain,(
% 1.49/0.56    k3_subset_1(sK0,sK1) = k1_subset_1(sK0) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_20)),
% 1.49/0.56    inference(subsumption_resolution,[],[f686,f101])).
% 1.49/0.56  fof(f101,plain,(
% 1.49/0.56    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 1.49/0.56    inference(avatar_component_clause,[],[f100])).
% 1.49/0.56  fof(f686,plain,(
% 1.49/0.56    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | k3_subset_1(sK0,sK1) = k1_subset_1(sK0) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_20),
% 1.49/0.56    inference(superposition,[],[f70,f270])).
% 1.49/0.56  fof(f270,plain,(
% 1.49/0.56    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_20),
% 1.49/0.56    inference(avatar_component_clause,[],[f268])).
% 1.49/0.56  fof(f70,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f44])).
% 1.49/0.56  fof(f44,plain,(
% 1.49/0.56    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(nnf_transformation,[],[f34])).
% 1.49/0.56  fof(f34,plain,(
% 1.49/0.56    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f24])).
% 1.49/0.56  fof(f24,axiom,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 1.49/0.56  fof(f685,plain,(
% 1.49/0.56    ~spl3_30 | spl3_38 | ~spl3_37),
% 1.49/0.56    inference(avatar_split_clause,[],[f680,f669,f682,f542])).
% 1.49/0.56  fof(f542,plain,(
% 1.49/0.56    spl3_30 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.49/0.56  fof(f682,plain,(
% 1.49/0.56    spl3_38 <=> k1_xboole_0 = k1_subset_1(sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.49/0.56  fof(f669,plain,(
% 1.49/0.56    spl3_37 <=> sK0 = k3_subset_1(sK0,k1_xboole_0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.49/0.56  fof(f680,plain,(
% 1.49/0.56    k1_xboole_0 = k1_subset_1(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl3_37),
% 1.49/0.56    inference(subsumption_resolution,[],[f677,f50])).
% 1.49/0.56  fof(f50,plain,(
% 1.49/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.49/0.56  fof(f677,plain,(
% 1.49/0.56    ~r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 = k1_subset_1(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl3_37),
% 1.49/0.56    inference(superposition,[],[f70,f671])).
% 1.49/0.56  fof(f671,plain,(
% 1.49/0.56    sK0 = k3_subset_1(sK0,k1_xboole_0) | ~spl3_37),
% 1.49/0.56    inference(avatar_component_clause,[],[f669])).
% 1.49/0.56  fof(f672,plain,(
% 1.49/0.56    spl3_37 | ~spl3_6 | ~spl3_7),
% 1.49/0.56    inference(avatar_split_clause,[],[f667,f143,f138,f669])).
% 1.49/0.56  fof(f138,plain,(
% 1.49/0.56    spl3_6 <=> k1_xboole_0 = k3_subset_1(sK0,sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.49/0.56  fof(f143,plain,(
% 1.49/0.56    spl3_7 <=> sK0 = k3_subset_1(sK0,k3_subset_1(sK0,sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.49/0.56  fof(f667,plain,(
% 1.49/0.56    sK0 = k3_subset_1(sK0,k1_xboole_0) | (~spl3_6 | ~spl3_7)),
% 1.49/0.56    inference(forward_demodulation,[],[f145,f140])).
% 1.49/0.56  fof(f140,plain,(
% 1.49/0.56    k1_xboole_0 = k3_subset_1(sK0,sK0) | ~spl3_6),
% 1.49/0.56    inference(avatar_component_clause,[],[f138])).
% 1.49/0.56  fof(f145,plain,(
% 1.49/0.56    sK0 = k3_subset_1(sK0,k3_subset_1(sK0,sK0)) | ~spl3_7),
% 1.49/0.56    inference(avatar_component_clause,[],[f143])).
% 1.49/0.56  fof(f620,plain,(
% 1.49/0.56    spl3_30 | ~spl3_4 | ~spl3_6),
% 1.49/0.56    inference(avatar_split_clause,[],[f619,f138,f117,f542])).
% 1.49/0.56  fof(f117,plain,(
% 1.49/0.56    spl3_4 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.49/0.56  fof(f619,plain,(
% 1.49/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | (~spl3_4 | ~spl3_6)),
% 1.49/0.56    inference(subsumption_resolution,[],[f618,f119])).
% 1.49/0.56  fof(f119,plain,(
% 1.49/0.56    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_4),
% 1.49/0.56    inference(avatar_component_clause,[],[f117])).
% 1.49/0.56  fof(f618,plain,(
% 1.49/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_6),
% 1.49/0.56    inference(superposition,[],[f67,f140])).
% 1.49/0.56  fof(f67,plain,(
% 1.49/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f31])).
% 1.49/0.56  fof(f31,plain,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f22])).
% 1.49/0.56  fof(f22,axiom,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.49/0.56  fof(f593,plain,(
% 1.49/0.56    spl3_6 | ~spl3_4),
% 1.49/0.56    inference(avatar_split_clause,[],[f592,f117,f138])).
% 1.49/0.56  fof(f592,plain,(
% 1.49/0.56    k1_xboole_0 = k3_subset_1(sK0,sK0) | ~spl3_4),
% 1.49/0.56    inference(forward_demodulation,[],[f591,f52])).
% 1.49/0.56  fof(f52,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.49/0.56  fof(f591,plain,(
% 1.49/0.56    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,sK0) | ~spl3_4),
% 1.49/0.56    inference(forward_demodulation,[],[f580,f92])).
% 1.49/0.56  fof(f92,plain,(
% 1.49/0.56    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 1.49/0.56    inference(definition_unfolding,[],[f58,f87])).
% 1.49/0.56  fof(f87,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f62,f86])).
% 1.49/0.56  fof(f86,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f59,f85])).
% 1.49/0.56  fof(f85,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f60,f84])).
% 1.49/0.56  fof(f84,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f72,f83])).
% 1.49/0.56  fof(f83,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f77,f82])).
% 1.49/0.56  fof(f82,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f78,f81])).
% 1.49/0.56  fof(f81,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f79,f80])).
% 1.49/0.56  fof(f80,plain,(
% 1.49/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f15])).
% 1.49/0.56  fof(f15,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.49/0.56  fof(f79,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f14])).
% 1.49/0.56  fof(f14,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.49/0.56  fof(f78,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f13])).
% 1.49/0.56  fof(f13,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.49/0.56  fof(f77,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f12])).
% 1.49/0.56  fof(f12,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.49/0.56  fof(f72,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f11])).
% 1.49/0.56  fof(f11,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.49/0.56  fof(f60,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f10])).
% 1.49/0.56  fof(f10,axiom,(
% 1.49/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.49/0.56  fof(f59,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f16])).
% 1.49/0.56  fof(f16,axiom,(
% 1.49/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.49/0.56  fof(f62,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f8])).
% 1.49/0.56  fof(f8,axiom,(
% 1.49/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.49/0.56  fof(f58,plain,(
% 1.49/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f28])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.49/0.56    inference(rectify,[],[f3])).
% 1.49/0.56  fof(f3,axiom,(
% 1.49/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.49/0.56  fof(f580,plain,(
% 1.49/0.56    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK0),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl3_4),
% 1.49/0.56    inference(resolution,[],[f119,f93])).
% 1.49/0.56  fof(f93,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f68,f88])).
% 1.49/0.56  fof(f88,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f61,f87])).
% 1.49/0.56  fof(f61,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f4])).
% 1.49/0.56  fof(f4,axiom,(
% 1.49/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.49/0.56  fof(f68,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f32])).
% 1.49/0.56  fof(f32,plain,(
% 1.49/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f21])).
% 1.49/0.56  fof(f21,axiom,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.49/0.56  fof(f590,plain,(
% 1.49/0.56    spl3_7 | ~spl3_4),
% 1.49/0.56    inference(avatar_split_clause,[],[f579,f117,f143])).
% 1.49/0.56  fof(f579,plain,(
% 1.49/0.56    sK0 = k3_subset_1(sK0,k3_subset_1(sK0,sK0)) | ~spl3_4),
% 1.49/0.56    inference(resolution,[],[f119,f69])).
% 1.49/0.56  fof(f69,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f33])).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f23])).
% 1.49/0.56  fof(f23,axiom,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.49/0.56  fof(f540,plain,(
% 1.49/0.56    spl3_4 | spl3_8 | ~spl3_9),
% 1.49/0.56    inference(avatar_split_clause,[],[f372,f156,f152,f117])).
% 1.49/0.56  fof(f152,plain,(
% 1.49/0.56    spl3_8 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.49/0.56  fof(f156,plain,(
% 1.49/0.56    spl3_9 <=> r2_hidden(sK0,k1_zfmisc_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.49/0.56  fof(f372,plain,(
% 1.49/0.56    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | (spl3_8 | ~spl3_9)),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f153,f158,f64])).
% 1.49/0.56  fof(f64,plain,(
% 1.49/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f43])).
% 1.49/0.56  fof(f43,plain,(
% 1.49/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.49/0.56    inference(nnf_transformation,[],[f30])).
% 1.49/0.56  fof(f30,plain,(
% 1.49/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f19])).
% 1.49/0.56  fof(f19,axiom,(
% 1.49/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.49/0.56  fof(f158,plain,(
% 1.49/0.56    r2_hidden(sK0,k1_zfmisc_1(sK0)) | ~spl3_9),
% 1.49/0.56    inference(avatar_component_clause,[],[f156])).
% 1.49/0.56  fof(f153,plain,(
% 1.49/0.56    ~v1_xboole_0(k1_zfmisc_1(sK0)) | spl3_8),
% 1.49/0.56    inference(avatar_component_clause,[],[f152])).
% 1.49/0.56  fof(f534,plain,(
% 1.49/0.56    spl3_9),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f528])).
% 1.49/0.56  fof(f528,plain,(
% 1.49/0.56    $false | spl3_9),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f90,f157,f95])).
% 1.49/0.56  fof(f95,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f75,f85])).
% 1.49/0.56  fof(f75,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f46])).
% 1.49/0.56  fof(f46,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.49/0.56    inference(flattening,[],[f45])).
% 1.49/0.56  fof(f45,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.49/0.56    inference(nnf_transformation,[],[f17])).
% 1.49/0.56  fof(f17,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.49/0.56  fof(f157,plain,(
% 1.49/0.56    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | spl3_9),
% 1.49/0.56    inference(avatar_component_clause,[],[f156])).
% 1.49/0.56  fof(f90,plain,(
% 1.49/0.56    ( ! [X0] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X0))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f53,f89])).
% 1.49/0.56  fof(f89,plain,(
% 1.49/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f54,f85])).
% 1.49/0.56  fof(f54,plain,(
% 1.49/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f9])).
% 1.49/0.56  fof(f9,axiom,(
% 1.49/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.49/0.56  fof(f53,plain,(
% 1.49/0.56    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f18,axiom,(
% 1.49/0.56    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 1.49/0.56  fof(f509,plain,(
% 1.49/0.56    ~spl3_6 | spl3_12),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f508])).
% 1.49/0.56  fof(f508,plain,(
% 1.49/0.56    $false | (~spl3_6 | spl3_12)),
% 1.49/0.56    inference(subsumption_resolution,[],[f504,f50])).
% 1.49/0.56  fof(f504,plain,(
% 1.49/0.56    ~r1_tarski(k1_xboole_0,sK0) | (~spl3_6 | spl3_12)),
% 1.49/0.56    inference(backward_demodulation,[],[f181,f140])).
% 1.49/0.56  fof(f181,plain,(
% 1.49/0.56    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_12),
% 1.49/0.56    inference(avatar_component_clause,[],[f179])).
% 1.49/0.56  fof(f179,plain,(
% 1.49/0.56    spl3_12 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.49/0.56  fof(f418,plain,(
% 1.49/0.56    ~spl3_8 | ~spl3_9),
% 1.49/0.56    inference(avatar_split_clause,[],[f373,f156,f152])).
% 1.49/0.56  fof(f373,plain,(
% 1.49/0.56    ~v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_9),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f158,f55])).
% 1.49/0.56  fof(f55,plain,(
% 1.49/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f42])).
% 1.49/0.56  fof(f42,plain,(
% 1.49/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 1.49/0.56  fof(f41,plain,(
% 1.49/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f40,plain,(
% 1.49/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.49/0.56    inference(rectify,[],[f39])).
% 1.49/0.56  fof(f39,plain,(
% 1.49/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.49/0.56    inference(nnf_transformation,[],[f1])).
% 1.49/0.56  fof(f1,axiom,(
% 1.49/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.49/0.56  fof(f272,plain,(
% 1.49/0.56    spl3_20 | ~spl3_3),
% 1.49/0.56    inference(avatar_split_clause,[],[f246,f111,f268])).
% 1.49/0.56  fof(f111,plain,(
% 1.49/0.56    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.49/0.56  fof(f246,plain,(
% 1.49/0.56    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_3),
% 1.49/0.56    inference(resolution,[],[f113,f69])).
% 1.49/0.56  fof(f113,plain,(
% 1.49/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.49/0.56    inference(avatar_component_clause,[],[f111])).
% 1.49/0.56  fof(f260,plain,(
% 1.49/0.56    spl3_18 | ~spl3_3),
% 1.49/0.56    inference(avatar_split_clause,[],[f243,f111,f257])).
% 1.49/0.56  fof(f243,plain,(
% 1.49/0.56    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f113,f67])).
% 1.49/0.56  fof(f182,plain,(
% 1.49/0.56    ~spl3_12 | spl3_1 | ~spl3_2),
% 1.49/0.56    inference(avatar_split_clause,[],[f177,f104,f100,f179])).
% 1.49/0.56  fof(f104,plain,(
% 1.49/0.56    spl3_2 <=> sK0 = sK1),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.49/0.56  fof(f177,plain,(
% 1.49/0.56    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl3_1 | ~spl3_2)),
% 1.49/0.56    inference(forward_demodulation,[],[f102,f105])).
% 1.49/0.56  fof(f105,plain,(
% 1.49/0.56    sK0 = sK1 | ~spl3_2),
% 1.49/0.56    inference(avatar_component_clause,[],[f104])).
% 1.49/0.56  fof(f102,plain,(
% 1.49/0.56    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_1),
% 1.49/0.56    inference(avatar_component_clause,[],[f100])).
% 1.49/0.56  fof(f114,plain,(
% 1.49/0.56    spl3_3),
% 1.49/0.56    inference(avatar_split_clause,[],[f47,f111])).
% 1.49/0.56  fof(f47,plain,(
% 1.49/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.49/0.56    inference(cnf_transformation,[],[f38])).
% 1.49/0.56  fof(f38,plain,(
% 1.49/0.56    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f37])).
% 1.49/0.56  fof(f37,plain,(
% 1.49/0.56    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f36,plain,(
% 1.49/0.56    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(flattening,[],[f35])).
% 1.49/0.56  fof(f35,plain,(
% 1.49/0.56    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(nnf_transformation,[],[f29])).
% 1.49/0.56  fof(f29,plain,(
% 1.49/0.56    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f26])).
% 1.49/0.56  fof(f26,negated_conjecture,(
% 1.49/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.49/0.56    inference(negated_conjecture,[],[f25])).
% 1.49/0.56  fof(f25,conjecture,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 1.49/0.56  fof(f109,plain,(
% 1.49/0.56    spl3_1 | spl3_2),
% 1.49/0.56    inference(avatar_split_clause,[],[f108,f104,f100])).
% 1.49/0.56  fof(f108,plain,(
% 1.49/0.56    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.49/0.56    inference(forward_demodulation,[],[f48,f51])).
% 1.49/0.56  fof(f51,plain,(
% 1.49/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  fof(f20,axiom,(
% 1.49/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.49/0.56  fof(f48,plain,(
% 1.49/0.56    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.49/0.56    inference(cnf_transformation,[],[f38])).
% 1.49/0.56  fof(f107,plain,(
% 1.49/0.56    ~spl3_1 | ~spl3_2),
% 1.49/0.56    inference(avatar_split_clause,[],[f98,f104,f100])).
% 1.49/0.56  fof(f98,plain,(
% 1.49/0.56    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.49/0.56    inference(forward_demodulation,[],[f49,f51])).
% 1.49/0.56  fof(f49,plain,(
% 1.49/0.56    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.49/0.56    inference(cnf_transformation,[],[f38])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (22478)------------------------------
% 1.49/0.56  % (22478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (22478)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (22478)Memory used [KB]: 6524
% 1.49/0.56  % (22478)Time elapsed: 0.128 s
% 1.49/0.56  % (22478)------------------------------
% 1.49/0.56  % (22478)------------------------------
% 1.49/0.56  % (22452)Success in time 0.198 s
%------------------------------------------------------------------------------
