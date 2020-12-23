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
% DateTime   : Thu Dec  3 12:45:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 439 expanded)
%              Number of leaves         :   37 ( 164 expanded)
%              Depth                    :   17
%              Number of atoms          :  304 ( 791 expanded)
%              Number of equality atoms :   71 ( 312 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1615,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f113,f118,f123,f189,f195,f218,f344,f479,f560,f587,f1529,f1554,f1608])).

fof(f1608,plain,
    ( spl3_1
    | ~ spl3_16
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f1607,f584,f341,f105])).

fof(f105,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f341,plain,
    ( spl3_16
  <=> sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f584,plain,
    ( spl3_33
  <=> r1_tarski(sK1,k5_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1607,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_16
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f1606,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f1606,plain,
    ( r1_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_16
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f1605,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1605,plain,
    ( r1_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK0)))
    | ~ spl3_16
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f1604,f343])).

fof(f343,plain,
    ( sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f341])).

fof(f1604,plain,
    ( r1_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))))
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f1575,f93])).

fof(f93,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f58,f84,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1575,plain,
    ( r1_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0)))))
    | ~ spl3_33 ),
    inference(resolution,[],[f585,f285])).

fof(f285,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,X2))
      | r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ) ),
    inference(forward_demodulation,[],[f102,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f74,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f64,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f61,f84])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f585,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK2,sK0))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f584])).

fof(f1554,plain,
    ( spl3_33
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f1523,f341,f186,f105,f584])).

fof(f186,plain,
    ( spl3_6
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1523,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_tarski(sK1,k5_xboole_0(sK2,sK0))
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(resolution,[],[f1286,f188])).

fof(f188,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f186])).

fof(f1286,plain,
    ( ! [X9] :
        ( ~ r1_tarski(X9,sK0)
        | ~ r1_xboole_0(X9,sK2)
        | r1_tarski(X9,k5_xboole_0(sK2,sK0)) )
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f1285,f53])).

fof(f1285,plain,
    ( ! [X9] :
        ( ~ r1_xboole_0(X9,k5_xboole_0(sK2,k1_xboole_0))
        | ~ r1_tarski(X9,sK0)
        | r1_tarski(X9,k5_xboole_0(sK2,sK0)) )
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f1279,f52])).

fof(f1279,plain,
    ( ! [X9] :
        ( ~ r1_tarski(X9,sK0)
        | r1_tarski(X9,k5_xboole_0(sK2,sK0))
        | ~ r1_xboole_0(X9,k5_xboole_0(sK2,k5_xboole_0(sK0,sK0))) )
    | ~ spl3_16 ),
    inference(superposition,[],[f371,f343])).

fof(f371,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))
      | r1_tarski(X2,k5_xboole_0(X0,X1))
      | ~ r1_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) ) ),
    inference(superposition,[],[f345,f93])).

fof(f345,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | r1_tarski(X0,k5_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ) ),
    inference(forward_demodulation,[],[f101,f69])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))
      | ~ r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f75,f86,f85])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1529,plain,
    ( sK0 != k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))
    | k3_subset_1(sK0,sK2) != k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | r1_tarski(sK1,k5_xboole_0(sK2,sK0))
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f587,plain,
    ( ~ spl3_33
    | spl3_2
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f570,f557,f109,f584])).

fof(f109,plain,
    ( spl3_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f557,plain,
    ( spl3_29
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f570,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK2,sK0))
    | spl3_2
    | ~ spl3_29 ),
    inference(backward_demodulation,[],[f111,f559])).

fof(f559,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,sK0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f557])).

fof(f111,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f560,plain,
    ( spl3_29
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f549,f475,f341,f557])).

fof(f475,plain,
    ( spl3_22
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f549,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,sK0)
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f477,f343])).

fof(f477,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f475])).

fof(f479,plain,
    ( spl3_22
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f464,f115,f475])).

fof(f115,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f464,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f440,f117])).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f440,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(backward_demodulation,[],[f298,f146])).

fof(f146,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f124,f140])).

fof(f140,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f133,f53])).

fof(f133,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f124,f52])).

fof(f124,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f69,f52])).

fof(f298,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ) ),
    inference(forward_demodulation,[],[f97,f69])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f66,f87])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f62,f86])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f344,plain,
    ( spl3_16
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f339,f214,f341])).

fof(f214,plain,
    ( spl3_10
  <=> sK0 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f339,plain,
    ( sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f216,f93])).

fof(f216,plain,
    ( sK0 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f214])).

fof(f218,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f212,f192,f214])).

fof(f192,plain,
    ( spl3_7
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f212,plain,
    ( sK0 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0))
    | ~ spl3_7 ),
    inference(resolution,[],[f194,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f65,f85])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f194,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f192])).

fof(f195,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f190,f115,f192])).

fof(f190,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f178,f89])).

fof(f89,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f51,f88])).

fof(f88,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f55,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f178,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f117,f49,f90,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f189,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f184,f120,f186])).

fof(f120,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f184,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f179,f89])).

fof(f179,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f122,f49,f90,f67])).

fof(f122,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f123,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f45,f120])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(sK1,sK2) )
    & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
            | ~ r1_xboole_0(sK1,X2) )
          & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
            | r1_xboole_0(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
          | ~ r1_xboole_0(sK1,X2) )
        & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
          | r1_xboole_0(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | ~ r1_xboole_0(sK1,sK2) )
      & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | r1_xboole_0(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f118,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f46,f115])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f47,f109,f105])).

fof(f47,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f112,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f48,f109,f105])).

fof(f48,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (25257)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (25263)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (25256)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (25252)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (25261)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (25251)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (25264)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (25262)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (25262)Refutation not found, incomplete strategy% (25262)------------------------------
% 0.21/0.52  % (25262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25262)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (25262)Memory used [KB]: 10618
% 0.21/0.52  % (25262)Time elapsed: 0.083 s
% 0.21/0.52  % (25262)------------------------------
% 0.21/0.52  % (25262)------------------------------
% 0.21/0.52  % (25255)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (25253)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (25259)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (25257)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1615,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f112,f113,f118,f123,f189,f195,f218,f344,f479,f560,f587,f1529,f1554,f1608])).
% 0.21/0.52  fof(f1608,plain,(
% 0.21/0.52    spl3_1 | ~spl3_16 | ~spl3_33),
% 0.21/0.52    inference(avatar_split_clause,[],[f1607,f584,f341,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl3_1 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f341,plain,(
% 0.21/0.52    spl3_16 <=> sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.52  fof(f584,plain,(
% 0.21/0.52    spl3_33 <=> r1_tarski(sK1,k5_xboole_0(sK2,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.52  fof(f1607,plain,(
% 0.21/0.52    r1_xboole_0(sK1,sK2) | (~spl3_16 | ~spl3_33)),
% 0.21/0.52    inference(forward_demodulation,[],[f1606,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.52  fof(f1606,plain,(
% 0.21/0.52    r1_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) | (~spl3_16 | ~spl3_33)),
% 0.21/0.52    inference(forward_demodulation,[],[f1605,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.52  fof(f1605,plain,(
% 0.21/0.52    r1_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK0))) | (~spl3_16 | ~spl3_33)),
% 0.21/0.52    inference(forward_demodulation,[],[f1604,f343])).
% 0.21/0.52  fof(f343,plain,(
% 0.21/0.52    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)) | ~spl3_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f341])).
% 0.21/0.52  fof(f1604,plain,(
% 0.21/0.52    r1_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))))) | ~spl3_33),
% 0.21/0.52    inference(forward_demodulation,[],[f1575,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f58,f84,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f60,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f68,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f76,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f77,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f78,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 1.48/0.54  fof(f20,axiom,(
% 1.48/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.48/0.54  fof(f78,plain,(
% 1.48/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f19])).
% 1.48/0.54  fof(f19,axiom,(
% 1.48/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.48/0.54  fof(f77,plain,(
% 1.48/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f18])).
% 1.48/0.54  fof(f18,axiom,(
% 1.48/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.48/0.54  fof(f76,plain,(
% 1.48/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f17])).
% 1.48/0.54  fof(f17,axiom,(
% 1.48/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.48/0.54  fof(f68,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f16])).
% 1.48/0.54  fof(f16,axiom,(
% 1.48/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.54  fof(f60,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f15])).
% 1.48/0.54  fof(f15,axiom,(
% 1.48/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.54  fof(f58,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f14])).
% 1.48/0.54  fof(f14,axiom,(
% 1.48/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.48/0.54  fof(f1575,plain,(
% 1.48/0.54    r1_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0))))) | ~spl3_33),
% 1.48/0.54    inference(resolution,[],[f585,f285])).
% 1.48/0.54  fof(f285,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,X2)) | r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))) )),
% 1.48/0.54    inference(forward_demodulation,[],[f102,f69])).
% 1.48/0.54  fof(f69,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f11])).
% 1.48/0.54  fof(f11,axiom,(
% 1.48/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.48/0.54  fof(f102,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 1.48/0.54    inference(definition_unfolding,[],[f74,f86])).
% 1.48/0.54  fof(f86,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.48/0.54    inference(definition_unfolding,[],[f64,f85])).
% 1.48/0.54  fof(f85,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.48/0.54    inference(definition_unfolding,[],[f61,f84])).
% 1.48/0.54  fof(f61,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f21])).
% 1.48/0.54  fof(f21,axiom,(
% 1.48/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.48/0.54  fof(f64,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f13])).
% 1.48/0.54  fof(f13,axiom,(
% 1.48/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.48/0.54  fof(f74,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f44])).
% 1.48/0.54  fof(f44,plain,(
% 1.48/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.48/0.54    inference(flattening,[],[f43])).
% 1.48/0.54  fof(f43,plain,(
% 1.48/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.48/0.54    inference(nnf_transformation,[],[f5])).
% 1.48/0.54  fof(f5,axiom,(
% 1.48/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 1.48/0.54  fof(f585,plain,(
% 1.48/0.54    r1_tarski(sK1,k5_xboole_0(sK2,sK0)) | ~spl3_33),
% 1.48/0.54    inference(avatar_component_clause,[],[f584])).
% 1.48/0.54  fof(f1554,plain,(
% 1.48/0.54    spl3_33 | ~spl3_1 | ~spl3_6 | ~spl3_16),
% 1.48/0.54    inference(avatar_split_clause,[],[f1523,f341,f186,f105,f584])).
% 1.48/0.54  fof(f186,plain,(
% 1.48/0.54    spl3_6 <=> r1_tarski(sK1,sK0)),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.48/0.54  fof(f1523,plain,(
% 1.48/0.54    ~r1_xboole_0(sK1,sK2) | r1_tarski(sK1,k5_xboole_0(sK2,sK0)) | (~spl3_6 | ~spl3_16)),
% 1.48/0.54    inference(resolution,[],[f1286,f188])).
% 1.48/0.54  fof(f188,plain,(
% 1.48/0.54    r1_tarski(sK1,sK0) | ~spl3_6),
% 1.48/0.54    inference(avatar_component_clause,[],[f186])).
% 1.48/0.54  fof(f1286,plain,(
% 1.48/0.54    ( ! [X9] : (~r1_tarski(X9,sK0) | ~r1_xboole_0(X9,sK2) | r1_tarski(X9,k5_xboole_0(sK2,sK0))) ) | ~spl3_16),
% 1.48/0.54    inference(forward_demodulation,[],[f1285,f53])).
% 1.48/0.54  fof(f1285,plain,(
% 1.48/0.54    ( ! [X9] : (~r1_xboole_0(X9,k5_xboole_0(sK2,k1_xboole_0)) | ~r1_tarski(X9,sK0) | r1_tarski(X9,k5_xboole_0(sK2,sK0))) ) | ~spl3_16),
% 1.48/0.54    inference(forward_demodulation,[],[f1279,f52])).
% 1.48/0.54  fof(f1279,plain,(
% 1.48/0.54    ( ! [X9] : (~r1_tarski(X9,sK0) | r1_tarski(X9,k5_xboole_0(sK2,sK0)) | ~r1_xboole_0(X9,k5_xboole_0(sK2,k5_xboole_0(sK0,sK0)))) ) | ~spl3_16),
% 1.48/0.54    inference(superposition,[],[f371,f343])).
% 1.48/0.54  fof(f371,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) | r1_tarski(X2,k5_xboole_0(X0,X1)) | ~r1_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) )),
% 1.48/0.54    inference(superposition,[],[f345,f93])).
% 1.48/0.54  fof(f345,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))) )),
% 1.48/0.54    inference(forward_demodulation,[],[f101,f69])).
% 1.48/0.54  fof(f101,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) | ~r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 1.48/0.54    inference(definition_unfolding,[],[f75,f86,f85])).
% 1.48/0.54  fof(f75,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f44])).
% 1.48/0.54  fof(f1529,plain,(
% 1.48/0.54    sK0 != k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)) | k3_subset_1(sK0,sK2) != k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | r1_tarski(sK1,k5_xboole_0(sK2,sK0)) | ~r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.48/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.48/0.54  fof(f587,plain,(
% 1.48/0.54    ~spl3_33 | spl3_2 | ~spl3_29),
% 1.48/0.54    inference(avatar_split_clause,[],[f570,f557,f109,f584])).
% 1.48/0.54  fof(f109,plain,(
% 1.48/0.54    spl3_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.48/0.54  fof(f557,plain,(
% 1.48/0.54    spl3_29 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,sK0)),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.48/0.54  fof(f570,plain,(
% 1.48/0.54    ~r1_tarski(sK1,k5_xboole_0(sK2,sK0)) | (spl3_2 | ~spl3_29)),
% 1.48/0.54    inference(backward_demodulation,[],[f111,f559])).
% 1.48/0.54  fof(f559,plain,(
% 1.48/0.54    k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,sK0) | ~spl3_29),
% 1.48/0.54    inference(avatar_component_clause,[],[f557])).
% 1.48/0.54  fof(f111,plain,(
% 1.48/0.54    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | spl3_2),
% 1.48/0.54    inference(avatar_component_clause,[],[f109])).
% 1.48/0.54  fof(f560,plain,(
% 1.48/0.54    spl3_29 | ~spl3_16 | ~spl3_22),
% 1.48/0.54    inference(avatar_split_clause,[],[f549,f475,f341,f557])).
% 1.48/0.54  fof(f475,plain,(
% 1.48/0.54    spl3_22 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.48/0.54  fof(f549,plain,(
% 1.48/0.54    k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,sK0) | (~spl3_16 | ~spl3_22)),
% 1.48/0.54    inference(backward_demodulation,[],[f477,f343])).
% 1.48/0.54  fof(f477,plain,(
% 1.48/0.54    k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | ~spl3_22),
% 1.48/0.54    inference(avatar_component_clause,[],[f475])).
% 1.48/0.54  fof(f479,plain,(
% 1.48/0.54    spl3_22 | ~spl3_3),
% 1.48/0.54    inference(avatar_split_clause,[],[f464,f115,f475])).
% 1.48/0.54  fof(f115,plain,(
% 1.48/0.54    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.48/0.54  fof(f464,plain,(
% 1.48/0.54    k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | ~spl3_3),
% 1.48/0.54    inference(resolution,[],[f440,f117])).
% 1.48/0.54  fof(f117,plain,(
% 1.48/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.48/0.54    inference(avatar_component_clause,[],[f115])).
% 1.48/0.54  fof(f440,plain,(
% 1.48/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.48/0.54    inference(backward_demodulation,[],[f298,f146])).
% 1.48/0.54  fof(f146,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.48/0.54    inference(backward_demodulation,[],[f124,f140])).
% 1.48/0.54  fof(f140,plain,(
% 1.48/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.48/0.54    inference(forward_demodulation,[],[f133,f53])).
% 1.48/0.54  fof(f133,plain,(
% 1.48/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.48/0.54    inference(superposition,[],[f124,f52])).
% 1.48/0.54  fof(f124,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.48/0.54    inference(superposition,[],[f69,f52])).
% 1.48/0.54  fof(f298,plain,(
% 1.48/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 1.48/0.54    inference(forward_demodulation,[],[f97,f69])).
% 1.48/0.54  fof(f97,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.48/0.54    inference(definition_unfolding,[],[f66,f87])).
% 1.48/0.54  fof(f87,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.48/0.54    inference(definition_unfolding,[],[f62,f86])).
% 1.48/0.54  fof(f62,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f4])).
% 1.48/0.54  fof(f4,axiom,(
% 1.48/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.48/0.54  fof(f66,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f34])).
% 1.48/0.54  fof(f34,plain,(
% 1.48/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f24])).
% 1.48/0.54  fof(f24,axiom,(
% 1.48/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.48/0.54  fof(f344,plain,(
% 1.48/0.54    spl3_16 | ~spl3_10),
% 1.48/0.54    inference(avatar_split_clause,[],[f339,f214,f341])).
% 1.48/0.54  fof(f214,plain,(
% 1.48/0.54    spl3_10 <=> sK0 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0))),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.48/0.54  fof(f339,plain,(
% 1.48/0.54    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)) | ~spl3_10),
% 1.48/0.54    inference(forward_demodulation,[],[f216,f93])).
% 1.48/0.54  fof(f216,plain,(
% 1.48/0.54    sK0 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0)) | ~spl3_10),
% 1.48/0.54    inference(avatar_component_clause,[],[f214])).
% 1.48/0.54  fof(f218,plain,(
% 1.48/0.54    spl3_10 | ~spl3_7),
% 1.48/0.54    inference(avatar_split_clause,[],[f212,f192,f214])).
% 1.48/0.54  fof(f192,plain,(
% 1.48/0.54    spl3_7 <=> r1_tarski(sK2,sK0)),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.48/0.54  fof(f212,plain,(
% 1.48/0.54    sK0 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0)) | ~spl3_7),
% 1.48/0.54    inference(resolution,[],[f194,f96])).
% 1.48/0.54  fof(f96,plain,(
% 1.48/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 1.48/0.54    inference(definition_unfolding,[],[f65,f85])).
% 1.48/0.54  fof(f65,plain,(
% 1.48/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f33])).
% 1.48/0.54  fof(f33,plain,(
% 1.48/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.48/0.54    inference(ennf_transformation,[],[f6])).
% 1.48/0.54  fof(f6,axiom,(
% 1.48/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.48/0.54  fof(f194,plain,(
% 1.48/0.54    r1_tarski(sK2,sK0) | ~spl3_7),
% 1.48/0.54    inference(avatar_component_clause,[],[f192])).
% 1.48/0.54  fof(f195,plain,(
% 1.48/0.54    spl3_7 | ~spl3_3),
% 1.48/0.54    inference(avatar_split_clause,[],[f190,f115,f192])).
% 1.48/0.54  fof(f190,plain,(
% 1.48/0.54    r1_tarski(sK2,sK0) | ~spl3_3),
% 1.48/0.54    inference(forward_demodulation,[],[f178,f89])).
% 1.48/0.54  fof(f89,plain,(
% 1.48/0.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.48/0.54    inference(definition_unfolding,[],[f51,f88])).
% 1.48/0.54  fof(f88,plain,(
% 1.48/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.48/0.54    inference(definition_unfolding,[],[f55,f50])).
% 1.48/0.54  fof(f50,plain,(
% 1.48/0.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f22])).
% 1.48/0.54  fof(f22,axiom,(
% 1.48/0.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.48/0.54  fof(f55,plain,(
% 1.48/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f26])).
% 1.48/0.54  fof(f26,axiom,(
% 1.48/0.54    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.48/0.54  fof(f51,plain,(
% 1.48/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.48/0.54    inference(cnf_transformation,[],[f23])).
% 1.48/0.54  fof(f23,axiom,(
% 1.48/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.48/0.54  fof(f178,plain,(
% 1.48/0.54    r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0)) | ~spl3_3),
% 1.48/0.54    inference(unit_resulting_resolution,[],[f117,f49,f90,f67])).
% 1.48/0.54  fof(f67,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,k3_subset_1(X0,X1))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f36])).
% 1.48/0.54  fof(f36,plain,(
% 1.48/0.54    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.48/0.54    inference(flattening,[],[f35])).
% 1.48/0.54  fof(f35,plain,(
% 1.48/0.54    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f27])).
% 1.48/0.54  fof(f27,axiom,(
% 1.48/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 1.48/0.54  fof(f90,plain,(
% 1.48/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.48/0.54    inference(definition_unfolding,[],[f54,f50])).
% 1.48/0.54  fof(f54,plain,(
% 1.48/0.54    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f25])).
% 1.48/0.54  fof(f25,axiom,(
% 1.48/0.54    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 1.48/0.54  fof(f49,plain,(
% 1.48/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f7])).
% 1.48/0.54  fof(f7,axiom,(
% 1.48/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.48/0.54  fof(f189,plain,(
% 1.48/0.54    spl3_6 | ~spl3_4),
% 1.48/0.54    inference(avatar_split_clause,[],[f184,f120,f186])).
% 1.48/0.54  fof(f120,plain,(
% 1.48/0.54    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.48/0.54  fof(f184,plain,(
% 1.48/0.54    r1_tarski(sK1,sK0) | ~spl3_4),
% 1.48/0.54    inference(forward_demodulation,[],[f179,f89])).
% 1.48/0.54  fof(f179,plain,(
% 1.48/0.54    r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0)) | ~spl3_4),
% 1.48/0.54    inference(unit_resulting_resolution,[],[f122,f49,f90,f67])).
% 1.48/0.54  fof(f122,plain,(
% 1.48/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 1.48/0.54    inference(avatar_component_clause,[],[f120])).
% 1.48/0.54  fof(f123,plain,(
% 1.48/0.54    spl3_4),
% 1.48/0.54    inference(avatar_split_clause,[],[f45,f120])).
% 1.48/0.54  fof(f45,plain,(
% 1.48/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.48/0.54    inference(cnf_transformation,[],[f42])).
% 1.48/0.54  fof(f42,plain,(
% 1.48/0.54    ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.48/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f41,f40])).
% 1.48/0.54  fof(f40,plain,(
% 1.48/0.54    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.48/0.54    introduced(choice_axiom,[])).
% 1.48/0.54  fof(f41,plain,(
% 1.48/0.54    ? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.48/0.54    introduced(choice_axiom,[])).
% 1.48/0.54  fof(f39,plain,(
% 1.48/0.54    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.48/0.54    inference(flattening,[],[f38])).
% 1.48/0.54  fof(f38,plain,(
% 1.48/0.54    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.48/0.54    inference(nnf_transformation,[],[f32])).
% 1.48/0.54  fof(f32,plain,(
% 1.48/0.54    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f29])).
% 1.48/0.54  fof(f29,negated_conjecture,(
% 1.48/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 1.48/0.54    inference(negated_conjecture,[],[f28])).
% 1.48/0.54  fof(f28,conjecture,(
% 1.48/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 1.48/0.54  fof(f118,plain,(
% 1.48/0.54    spl3_3),
% 1.48/0.54    inference(avatar_split_clause,[],[f46,f115])).
% 1.48/0.54  fof(f46,plain,(
% 1.48/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.48/0.54    inference(cnf_transformation,[],[f42])).
% 1.48/0.54  fof(f113,plain,(
% 1.48/0.54    spl3_1 | spl3_2),
% 1.48/0.54    inference(avatar_split_clause,[],[f47,f109,f105])).
% 1.48/0.54  fof(f47,plain,(
% 1.48/0.54    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 1.48/0.54    inference(cnf_transformation,[],[f42])).
% 1.48/0.54  fof(f112,plain,(
% 1.48/0.54    ~spl3_1 | ~spl3_2),
% 1.48/0.54    inference(avatar_split_clause,[],[f48,f109,f105])).
% 1.48/0.54  fof(f48,plain,(
% 1.48/0.54    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 1.48/0.54    inference(cnf_transformation,[],[f42])).
% 1.48/0.54  % SZS output end Proof for theBenchmark
% 1.48/0.54  % (25257)------------------------------
% 1.48/0.54  % (25257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.54  % (25257)Termination reason: Refutation
% 1.48/0.54  
% 1.48/0.54  % (25257)Memory used [KB]: 7419
% 1.48/0.54  % (25257)Time elapsed: 0.122 s
% 1.48/0.54  % (25257)------------------------------
% 1.48/0.54  % (25257)------------------------------
% 1.48/0.54  % (25258)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.48/0.54  % (25266)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.48/0.54  % (25248)Success in time 0.187 s
%------------------------------------------------------------------------------
