%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:35 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 190 expanded)
%              Number of leaves         :   33 (  78 expanded)
%              Depth                    :    8
%              Number of atoms          :  254 ( 419 expanded)
%              Number of equality atoms :   63 ( 108 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f595,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f174,f182,f191,f205,f209,f224,f270,f276,f297,f315,f545,f557,f589])).

fof(f589,plain,
    ( spl3_11
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f588,f554,f144])).

fof(f144,plain,
    ( spl3_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f554,plain,
    ( spl3_56
  <=> k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f588,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f580,f111])).

fof(f111,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f56,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f580,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_56 ),
    inference(superposition,[],[f202,f556])).

fof(f556,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f554])).

fof(f202,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f198,f111])).

fof(f198,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f57,f39])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f44,f45,f45])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f557,plain,
    ( spl3_56
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f552,f542,f554])).

fof(f542,plain,
    ( spl3_55
  <=> v1_xboole_0(k4_xboole_0(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f552,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_55 ),
    inference(resolution,[],[f544,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f544,plain,
    ( v1_xboole_0(k4_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f542])).

fof(f545,plain,
    ( spl3_55
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f538,f294,f542])).

fof(f294,plain,
    ( spl3_28
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f538,plain,
    ( v1_xboole_0(k4_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_28 ),
    inference(resolution,[],[f115,f525])).

fof(f525,plain,
    ( ! [X14] : r1_tarski(k4_xboole_0(sK1,X14),k1_xboole_0)
    | ~ spl3_28 ),
    inference(resolution,[],[f125,f296])).

fof(f296,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f294])).

fof(f125,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | r1_tarski(k4_xboole_0(X3,X5),X4) ) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
      | v1_xboole_0(k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f315,plain,
    ( k8_setfam_1(sK0,sK2) != k1_setfam_1(sK2)
    | k8_setfam_1(sK0,sK1) != k6_setfam_1(sK0,sK1)
    | k1_setfam_1(sK1) != k6_setfam_1(sK0,sK1)
    | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f297,plain,
    ( spl3_28
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f278,f158,f71,f294])).

fof(f71,plain,
    ( spl3_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f158,plain,
    ( spl3_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f278,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f73,f160])).

fof(f160,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f158])).

fof(f73,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f276,plain,
    ( spl3_14
    | spl3_26
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f271,f179,f76,f273,f158])).

fof(f273,plain,
    ( spl3_26
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f76,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f179,plain,
    ( spl3_16
  <=> k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f271,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f265,f181])).

fof(f181,plain,
    ( k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f265,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f52,f78])).

fof(f78,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f270,plain,
    ( spl3_25
    | spl3_11
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f264,f61,f144,f267])).

fof(f267,plain,
    ( spl3_25
  <=> k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f61,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f264,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f52,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f224,plain,
    ( spl3_19
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f213,f61,f221])).

fof(f221,plain,
    ( spl3_19
  <=> k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f213,plain,
    ( k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f209,plain,
    ( spl3_10
    | spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f206,f71,f144,f140])).

fof(f140,plain,
    ( spl3_10
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f206,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f73,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f205,plain,
    ( spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f204,f188,f171])).

fof(f171,plain,
    ( spl3_15
  <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f188,plain,
    ( spl3_17
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f204,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl3_17 ),
    inference(resolution,[],[f190,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f190,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f188])).

fof(f191,plain,
    ( spl3_17
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f185,f76,f188])).

fof(f185,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f50,f78])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f182,plain,
    ( spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f177,f76,f179])).

fof(f177,plain,
    ( k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f49,f78])).

fof(f174,plain,
    ( ~ spl3_15
    | spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f169,f144,f66,f171])).

fof(f66,plain,
    ( spl3_2
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f169,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | spl3_2
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f163,f132])).

fof(f132,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f59,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f163,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_2
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f68,f146])).

fof(f146,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f68,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f79,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f74,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f37,f61])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (1667)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (1654)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.18/0.52  % (1655)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.18/0.52  % (1675)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.18/0.53  % (1672)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.18/0.53  % (1683)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.18/0.53  % (1665)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.18/0.53  % (1657)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.53  % (1658)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.53  % (1677)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.53  % (1668)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.54  % (1684)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (1663)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (1681)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.54  % (1666)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (1679)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.54  % (1659)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.54  % (1653)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.54  % (1676)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.55  % (1673)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.55  % (1680)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.55  % (1664)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (1671)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.56  % (1682)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.56  % (1674)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.56  % (1671)Refutation found. Thanks to Tanya!
% 1.35/0.56  % SZS status Theorem for theBenchmark
% 1.35/0.56  % (1661)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.56  % (1652)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.56  % (1669)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.58  % (1678)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.58  % (1660)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.58  % SZS output start Proof for theBenchmark
% 1.35/0.58  fof(f595,plain,(
% 1.35/0.58    $false),
% 1.35/0.58    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f174,f182,f191,f205,f209,f224,f270,f276,f297,f315,f545,f557,f589])).
% 1.35/0.58  fof(f589,plain,(
% 1.35/0.58    spl3_11 | ~spl3_56),
% 1.35/0.58    inference(avatar_split_clause,[],[f588,f554,f144])).
% 1.35/0.58  fof(f144,plain,(
% 1.35/0.58    spl3_11 <=> k1_xboole_0 = sK1),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.35/0.58  fof(f554,plain,(
% 1.35/0.58    spl3_56 <=> k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 1.35/0.58  fof(f588,plain,(
% 1.35/0.58    k1_xboole_0 = sK1 | ~spl3_56),
% 1.35/0.58    inference(forward_demodulation,[],[f580,f111])).
% 1.35/0.58  fof(f111,plain,(
% 1.35/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.58    inference(forward_demodulation,[],[f56,f39])).
% 1.35/0.58  fof(f39,plain,(
% 1.35/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f7])).
% 1.35/0.58  fof(f7,axiom,(
% 1.35/0.58    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.35/0.58  fof(f56,plain,(
% 1.35/0.58    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.35/0.58    inference(definition_unfolding,[],[f40,f45])).
% 1.35/0.58  fof(f45,plain,(
% 1.35/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.35/0.58    inference(cnf_transformation,[],[f10])).
% 1.35/0.58  fof(f10,axiom,(
% 1.35/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.35/0.58  fof(f40,plain,(
% 1.35/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.58    inference(cnf_transformation,[],[f4])).
% 1.35/0.58  fof(f4,axiom,(
% 1.35/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.35/0.58  fof(f580,plain,(
% 1.35/0.58    sK1 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_56),
% 1.35/0.58    inference(superposition,[],[f202,f556])).
% 1.35/0.58  fof(f556,plain,(
% 1.35/0.58    k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) | ~spl3_56),
% 1.35/0.58    inference(avatar_component_clause,[],[f554])).
% 1.35/0.58  fof(f202,plain,(
% 1.35/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.35/0.58    inference(forward_demodulation,[],[f198,f111])).
% 1.35/0.58  fof(f198,plain,(
% 1.35/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.35/0.58    inference(superposition,[],[f57,f39])).
% 1.35/0.58  fof(f57,plain,(
% 1.35/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 1.35/0.58    inference(definition_unfolding,[],[f44,f45,f45])).
% 1.35/0.58  fof(f44,plain,(
% 1.35/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f1])).
% 1.35/0.58  fof(f1,axiom,(
% 1.35/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.35/0.58  fof(f557,plain,(
% 1.35/0.58    spl3_56 | ~spl3_55),
% 1.35/0.58    inference(avatar_split_clause,[],[f552,f542,f554])).
% 1.35/0.58  fof(f542,plain,(
% 1.35/0.58    spl3_55 <=> v1_xboole_0(k4_xboole_0(sK1,k1_xboole_0))),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 1.35/0.58  fof(f552,plain,(
% 1.35/0.58    k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) | ~spl3_55),
% 1.35/0.58    inference(resolution,[],[f544,f41])).
% 1.35/0.58  fof(f41,plain,(
% 1.35/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.35/0.58    inference(cnf_transformation,[],[f23])).
% 1.35/0.58  fof(f23,plain,(
% 1.35/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.35/0.58    inference(ennf_transformation,[],[f2])).
% 1.35/0.58  fof(f2,axiom,(
% 1.35/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.35/0.58  fof(f544,plain,(
% 1.35/0.58    v1_xboole_0(k4_xboole_0(sK1,k1_xboole_0)) | ~spl3_55),
% 1.35/0.58    inference(avatar_component_clause,[],[f542])).
% 1.35/0.58  fof(f545,plain,(
% 1.35/0.58    spl3_55 | ~spl3_28),
% 1.35/0.58    inference(avatar_split_clause,[],[f538,f294,f542])).
% 1.35/0.58  fof(f294,plain,(
% 1.35/0.58    spl3_28 <=> r1_tarski(sK1,k1_xboole_0)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.35/0.58  fof(f538,plain,(
% 1.35/0.58    v1_xboole_0(k4_xboole_0(sK1,k1_xboole_0)) | ~spl3_28),
% 1.35/0.58    inference(resolution,[],[f115,f525])).
% 1.35/0.58  fof(f525,plain,(
% 1.35/0.58    ( ! [X14] : (r1_tarski(k4_xboole_0(sK1,X14),k1_xboole_0)) ) | ~spl3_28),
% 1.35/0.58    inference(resolution,[],[f125,f296])).
% 1.35/0.58  fof(f296,plain,(
% 1.35/0.58    r1_tarski(sK1,k1_xboole_0) | ~spl3_28),
% 1.35/0.58    inference(avatar_component_clause,[],[f294])).
% 1.35/0.58  fof(f125,plain,(
% 1.35/0.58    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | r1_tarski(k4_xboole_0(X3,X5),X4)) )),
% 1.35/0.58    inference(resolution,[],[f55,f43])).
% 1.35/0.58  fof(f43,plain,(
% 1.35/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f6])).
% 1.35/0.58  fof(f6,axiom,(
% 1.35/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.35/0.58  fof(f55,plain,(
% 1.35/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f33])).
% 1.35/0.58  fof(f33,plain,(
% 1.35/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.35/0.58    inference(flattening,[],[f32])).
% 1.35/0.58  fof(f32,plain,(
% 1.35/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.35/0.58    inference(ennf_transformation,[],[f5])).
% 1.35/0.58  fof(f5,axiom,(
% 1.35/0.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.35/0.58  fof(f115,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X1) | v1_xboole_0(k4_xboole_0(X0,X1))) )),
% 1.35/0.58    inference(resolution,[],[f46,f42])).
% 1.35/0.58  fof(f42,plain,(
% 1.35/0.58    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f9])).
% 1.35/0.58  fof(f9,axiom,(
% 1.35/0.58    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.35/0.58  fof(f46,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f25])).
% 1.35/0.58  fof(f25,plain,(
% 1.35/0.58    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.35/0.58    inference(flattening,[],[f24])).
% 1.35/0.58  fof(f24,plain,(
% 1.35/0.58    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.35/0.58    inference(ennf_transformation,[],[f8])).
% 1.35/0.58  fof(f8,axiom,(
% 1.35/0.58    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.35/0.58  fof(f315,plain,(
% 1.35/0.58    k8_setfam_1(sK0,sK2) != k1_setfam_1(sK2) | k8_setfam_1(sK0,sK1) != k6_setfam_1(sK0,sK1) | k1_setfam_1(sK1) != k6_setfam_1(sK0,sK1) | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 1.35/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.35/0.58  fof(f297,plain,(
% 1.35/0.58    spl3_28 | ~spl3_3 | ~spl3_14),
% 1.35/0.58    inference(avatar_split_clause,[],[f278,f158,f71,f294])).
% 1.35/0.58  fof(f71,plain,(
% 1.35/0.58    spl3_3 <=> r1_tarski(sK1,sK2)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.35/0.58  fof(f158,plain,(
% 1.35/0.58    spl3_14 <=> k1_xboole_0 = sK2),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.35/0.58  fof(f278,plain,(
% 1.35/0.58    r1_tarski(sK1,k1_xboole_0) | (~spl3_3 | ~spl3_14)),
% 1.35/0.58    inference(backward_demodulation,[],[f73,f160])).
% 1.35/0.58  fof(f160,plain,(
% 1.35/0.58    k1_xboole_0 = sK2 | ~spl3_14),
% 1.35/0.58    inference(avatar_component_clause,[],[f158])).
% 1.35/0.58  fof(f73,plain,(
% 1.35/0.58    r1_tarski(sK1,sK2) | ~spl3_3),
% 1.35/0.58    inference(avatar_component_clause,[],[f71])).
% 1.35/0.58  fof(f276,plain,(
% 1.35/0.58    spl3_14 | spl3_26 | ~spl3_4 | ~spl3_16),
% 1.35/0.58    inference(avatar_split_clause,[],[f271,f179,f76,f273,f158])).
% 1.35/0.58  fof(f273,plain,(
% 1.35/0.58    spl3_26 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.35/0.58  fof(f76,plain,(
% 1.35/0.58    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.35/0.58  fof(f179,plain,(
% 1.35/0.58    spl3_16 <=> k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.35/0.58  fof(f271,plain,(
% 1.35/0.58    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2 | (~spl3_4 | ~spl3_16)),
% 1.35/0.58    inference(forward_demodulation,[],[f265,f181])).
% 1.35/0.58  fof(f181,plain,(
% 1.35/0.58    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) | ~spl3_16),
% 1.35/0.58    inference(avatar_component_clause,[],[f179])).
% 1.35/0.58  fof(f265,plain,(
% 1.35/0.58    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl3_4),
% 1.35/0.58    inference(resolution,[],[f52,f78])).
% 1.35/0.58  fof(f78,plain,(
% 1.35/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 1.35/0.58    inference(avatar_component_clause,[],[f76])).
% 1.35/0.58  fof(f52,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f31])).
% 1.35/0.58  fof(f31,plain,(
% 1.35/0.58    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.58    inference(ennf_transformation,[],[f12])).
% 1.35/0.58  fof(f12,axiom,(
% 1.35/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.35/0.58  fof(f270,plain,(
% 1.35/0.58    spl3_25 | spl3_11 | ~spl3_1),
% 1.35/0.58    inference(avatar_split_clause,[],[f264,f61,f144,f267])).
% 1.35/0.58  fof(f267,plain,(
% 1.35/0.58    spl3_25 <=> k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.35/0.58  fof(f61,plain,(
% 1.35/0.58    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.35/0.58  fof(f264,plain,(
% 1.35/0.58    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | ~spl3_1),
% 1.35/0.58    inference(resolution,[],[f52,f63])).
% 1.35/0.58  fof(f63,plain,(
% 1.35/0.58    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_1),
% 1.35/0.58    inference(avatar_component_clause,[],[f61])).
% 1.35/0.58  fof(f224,plain,(
% 1.35/0.58    spl3_19 | ~spl3_1),
% 1.35/0.58    inference(avatar_split_clause,[],[f213,f61,f221])).
% 1.35/0.58  fof(f221,plain,(
% 1.35/0.58    spl3_19 <=> k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.35/0.58  fof(f213,plain,(
% 1.35/0.58    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) | ~spl3_1),
% 1.35/0.58    inference(resolution,[],[f63,f49])).
% 1.35/0.58  fof(f49,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f29])).
% 1.35/0.58  fof(f29,plain,(
% 1.35/0.58    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.58    inference(ennf_transformation,[],[f14])).
% 1.35/0.58  fof(f14,axiom,(
% 1.35/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.35/0.58  fof(f209,plain,(
% 1.35/0.58    spl3_10 | spl3_11 | ~spl3_3),
% 1.35/0.58    inference(avatar_split_clause,[],[f206,f71,f144,f140])).
% 1.35/0.58  fof(f140,plain,(
% 1.35/0.58    spl3_10 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.35/0.58  fof(f206,plain,(
% 1.35/0.58    k1_xboole_0 = sK1 | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | ~spl3_3),
% 1.35/0.58    inference(resolution,[],[f73,f47])).
% 1.35/0.58  fof(f47,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 1.35/0.58    inference(cnf_transformation,[],[f27])).
% 1.35/0.58  fof(f27,plain,(
% 1.35/0.58    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.35/0.58    inference(flattening,[],[f26])).
% 1.35/0.58  fof(f26,plain,(
% 1.35/0.58    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.35/0.58    inference(ennf_transformation,[],[f17])).
% 1.35/0.58  fof(f17,axiom,(
% 1.35/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.35/0.58  fof(f205,plain,(
% 1.35/0.58    spl3_15 | ~spl3_17),
% 1.35/0.58    inference(avatar_split_clause,[],[f204,f188,f171])).
% 1.35/0.58  fof(f171,plain,(
% 1.35/0.58    spl3_15 <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.35/0.58  fof(f188,plain,(
% 1.35/0.58    spl3_17 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.35/0.58  fof(f204,plain,(
% 1.35/0.58    r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl3_17),
% 1.35/0.58    inference(resolution,[],[f190,f54])).
% 1.35/0.58  fof(f54,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f15])).
% 1.35/0.58  fof(f15,axiom,(
% 1.35/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.35/0.58  fof(f190,plain,(
% 1.35/0.58    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_17),
% 1.35/0.58    inference(avatar_component_clause,[],[f188])).
% 1.35/0.58  fof(f191,plain,(
% 1.35/0.58    spl3_17 | ~spl3_4),
% 1.35/0.58    inference(avatar_split_clause,[],[f185,f76,f188])).
% 1.35/0.58  fof(f185,plain,(
% 1.35/0.58    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_4),
% 1.35/0.58    inference(resolution,[],[f50,f78])).
% 1.35/0.58  fof(f50,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.35/0.58    inference(cnf_transformation,[],[f30])).
% 1.35/0.58  fof(f30,plain,(
% 1.35/0.58    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.58    inference(ennf_transformation,[],[f13])).
% 1.35/0.58  fof(f13,axiom,(
% 1.35/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.35/0.58  fof(f182,plain,(
% 1.35/0.58    spl3_16 | ~spl3_4),
% 1.35/0.58    inference(avatar_split_clause,[],[f177,f76,f179])).
% 1.35/0.58  fof(f177,plain,(
% 1.35/0.58    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) | ~spl3_4),
% 1.35/0.58    inference(resolution,[],[f49,f78])).
% 1.35/0.58  fof(f174,plain,(
% 1.35/0.58    ~spl3_15 | spl3_2 | ~spl3_11),
% 1.35/0.58    inference(avatar_split_clause,[],[f169,f144,f66,f171])).
% 1.35/0.58  fof(f66,plain,(
% 1.35/0.58    spl3_2 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.35/0.58  fof(f169,plain,(
% 1.35/0.58    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | (spl3_2 | ~spl3_11)),
% 1.35/0.58    inference(forward_demodulation,[],[f163,f132])).
% 1.35/0.58  fof(f132,plain,(
% 1.35/0.58    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.35/0.58    inference(resolution,[],[f59,f38])).
% 1.35/0.58  fof(f38,plain,(
% 1.35/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.35/0.58    inference(cnf_transformation,[],[f11])).
% 1.35/0.58  fof(f11,axiom,(
% 1.35/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.35/0.58  fof(f59,plain,(
% 1.35/0.58    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.35/0.58    inference(equality_resolution,[],[f51])).
% 1.35/0.58  fof(f51,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 1.35/0.58    inference(cnf_transformation,[],[f31])).
% 1.35/0.58  fof(f163,plain,(
% 1.35/0.58    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_2 | ~spl3_11)),
% 1.35/0.58    inference(backward_demodulation,[],[f68,f146])).
% 1.35/0.58  fof(f146,plain,(
% 1.35/0.58    k1_xboole_0 = sK1 | ~spl3_11),
% 1.35/0.58    inference(avatar_component_clause,[],[f144])).
% 1.35/0.58  fof(f68,plain,(
% 1.35/0.58    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_2),
% 1.35/0.58    inference(avatar_component_clause,[],[f66])).
% 1.35/0.58  fof(f79,plain,(
% 1.35/0.58    spl3_4),
% 1.35/0.58    inference(avatar_split_clause,[],[f34,f76])).
% 1.35/0.58  fof(f34,plain,(
% 1.35/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.58    inference(cnf_transformation,[],[f22])).
% 1.35/0.58  fof(f22,plain,(
% 1.35/0.58    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.58    inference(flattening,[],[f21])).
% 1.35/0.58  fof(f21,plain,(
% 1.35/0.58    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.58    inference(ennf_transformation,[],[f19])).
% 1.35/0.58  fof(f19,negated_conjecture,(
% 1.35/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.35/0.58    inference(negated_conjecture,[],[f18])).
% 1.35/0.58  fof(f18,conjecture,(
% 1.35/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 1.35/0.58  fof(f74,plain,(
% 1.35/0.58    spl3_3),
% 1.35/0.58    inference(avatar_split_clause,[],[f35,f71])).
% 1.35/0.58  fof(f35,plain,(
% 1.35/0.58    r1_tarski(sK1,sK2)),
% 1.35/0.58    inference(cnf_transformation,[],[f22])).
% 1.35/0.58  fof(f69,plain,(
% 1.35/0.58    ~spl3_2),
% 1.35/0.58    inference(avatar_split_clause,[],[f36,f66])).
% 1.35/0.58  fof(f36,plain,(
% 1.35/0.58    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.35/0.58    inference(cnf_transformation,[],[f22])).
% 1.35/0.58  fof(f64,plain,(
% 1.35/0.58    spl3_1),
% 1.35/0.58    inference(avatar_split_clause,[],[f37,f61])).
% 1.35/0.58  fof(f37,plain,(
% 1.35/0.58    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.58    inference(cnf_transformation,[],[f22])).
% 1.35/0.58  % SZS output end Proof for theBenchmark
% 1.35/0.58  % (1671)------------------------------
% 1.35/0.58  % (1671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.58  % (1671)Termination reason: Refutation
% 1.35/0.58  
% 1.35/0.58  % (1671)Memory used [KB]: 11001
% 1.35/0.58  % (1671)Time elapsed: 0.156 s
% 1.35/0.58  % (1671)------------------------------
% 1.35/0.58  % (1671)------------------------------
% 1.35/0.59  % (1651)Success in time 0.226 s
%------------------------------------------------------------------------------
