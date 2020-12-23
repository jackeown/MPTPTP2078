%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:46 EST 2020

% Result     : Theorem 9.08s
% Output     : Refutation 9.08s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 486 expanded)
%              Number of leaves         :   18 ( 142 expanded)
%              Depth                    :   16
%              Number of atoms          :  235 ( 935 expanded)
%              Number of equality atoms :   41 ( 267 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f198,f750,f1928,f5262,f6188,f6233])).

fof(f6233,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f6232])).

fof(f6232,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f6231,f196])).

fof(f196,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f6231,plain,
    ( r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f6225,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f6225,plain,
    ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f193,f749,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f749,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f747])).

fof(f747,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f193,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f6188,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f6187])).

fof(f6187,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f6181,f197])).

fof(f197,plain,
    ( r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f195])).

fof(f6181,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | spl3_3 ),
    inference(superposition,[],[f5270,f58])).

fof(f5270,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f748,f440])).

fof(f440,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_tarski(X9,k4_xboole_0(X8,X7))
      | r1_xboole_0(X9,X7) ) ),
    inference(superposition,[],[f49,f326])).

fof(f326,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(subsumption_resolution,[],[f314,f236])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,k4_xboole_0(X0,X1))
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f186,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f186,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(k4_xboole_0(X0,X1),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f314,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0
      | r2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ) ),
    inference(resolution,[],[f263,f45])).

fof(f263,plain,(
    ! [X0,X1] : r1_tarski(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f65,f134,f50])).

fof(f134,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f65,f49])).

fof(f65,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f36,f60])).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f57,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f748,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f747])).

fof(f5262,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f5261])).

fof(f5261,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f5210,f2053])).

fof(f2053,plain,(
    ! [X85,X83,X84] : r1_xboole_0(k4_xboole_0(X85,k2_xboole_0(X83,X84)),k2_xboole_0(k4_xboole_0(X83,X84),k4_xboole_0(X84,X83))) ),
    inference(superposition,[],[f943,f58])).

fof(f943,plain,(
    ! [X6,X4,X5] : r1_xboole_0(k4_xboole_0(X6,X4),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f907,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f36,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f907,plain,(
    ! [X50,X51,X49] : r1_xboole_0(k4_xboole_0(X50,k2_xboole_0(X49,X51)),X49) ),
    inference(superposition,[],[f134,f722])).

fof(f722,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X5))) = X3 ),
    inference(subsumption_resolution,[],[f706,f236])).

fof(f706,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X5))) = X3
      | r2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X5)))) ) ),
    inference(resolution,[],[f268,f45])).

fof(f268,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2)))) ),
    inference(unit_resulting_resolution,[],[f65,f136,f50])).

fof(f136,plain,(
    ! [X2,X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(unit_resulting_resolution,[],[f92,f49])).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f5210,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f2134,f205])).

fof(f205,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)) = k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f197,f44])).

fof(f2134,plain,
    ( ! [X0] : ~ r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,X0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f936,f1947,f50])).

fof(f1947,plain,
    ( ! [X0,X1] : ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(sK0,X1)))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f921,f1937,f294])).

fof(f294,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X3,X2)
      | r1_tarski(X3,k1_xboole_0)
      | ~ r1_tarski(X3,X2) ) ),
    inference(superposition,[],[f50,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f55,f60])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f1937,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f1929,f1931,f45])).

fof(f1931,plain,
    ( ~ r2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f1929,f199])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r2_xboole_0(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f188,f43])).

fof(f188,plain,(
    ! [X3] :
      ( r2_xboole_0(k1_xboole_0,X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f45,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f36,f61])).

fof(f1929,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f192,f46])).

fof(f192,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f191])).

fof(f921,plain,(
    ! [X97,X95,X98,X96] : r1_xboole_0(k4_xboole_0(X95,X98),k4_xboole_0(X96,k2_xboole_0(X95,X97))) ),
    inference(superposition,[],[f445,f722])).

fof(f445,plain,(
    ! [X26,X24,X25] : r1_xboole_0(k4_xboole_0(k4_xboole_0(X25,X24),X26),X24) ),
    inference(superposition,[],[f133,f326])).

fof(f133,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(unit_resulting_resolution,[],[f36,f49])).

fof(f936,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f36,f907,f50])).

fof(f1928,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f64,f195,f747,f191])).

fof(f64,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f52,f58])).

fof(f52,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f34,f40,f51])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f34,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
      | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
        & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
            & r1_tarski(X0,k2_xboole_0(X1,X2)) )
          | r1_tarski(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
          & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
        | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <~> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
      <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f750,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f63,f195,f747])).

fof(f63,plain,
    ( r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f53,f58])).

fof(f53,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f33,f40,f51])).

fof(f33,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f198,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f62,f195,f191])).

fof(f62,plain,
    ( r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f54,f58])).

fof(f54,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f32,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (12621)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.49  % (12613)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (12616)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (12629)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (12608)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (12610)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (12601)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (12626)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (12604)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (12603)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (12622)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (12614)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (12600)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (12606)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (12615)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (12611)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (12618)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.56  % (12602)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.56  % (12612)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (12627)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (12607)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.57  % (12624)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.57  % (12617)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.57  % (12622)Refutation not found, incomplete strategy% (12622)------------------------------
% 0.20/0.57  % (12622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (12622)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (12622)Memory used [KB]: 10746
% 0.20/0.57  % (12622)Time elapsed: 0.121 s
% 0.20/0.57  % (12622)------------------------------
% 0.20/0.57  % (12622)------------------------------
% 0.20/0.57  % (12617)Refutation not found, incomplete strategy% (12617)------------------------------
% 0.20/0.57  % (12617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (12617)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (12617)Memory used [KB]: 10618
% 0.20/0.57  % (12617)Time elapsed: 0.157 s
% 0.20/0.57  % (12617)------------------------------
% 0.20/0.57  % (12617)------------------------------
% 0.20/0.57  % (12619)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.57  % (12609)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.58  % (12625)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.71/0.58  % (12623)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.71/0.59  % (12605)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.83/0.60  % (12620)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.83/0.61  % (12628)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.04/0.71  % (12663)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.04/0.72  % (12662)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.32/0.84  % (12605)Time limit reached!
% 3.32/0.84  % (12605)------------------------------
% 3.32/0.84  % (12605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.86  % (12605)Termination reason: Time limit
% 3.32/0.86  % (12605)Termination phase: Saturation
% 3.32/0.86  
% 3.32/0.86  % (12605)Memory used [KB]: 8443
% 3.32/0.86  % (12605)Time elapsed: 0.400 s
% 3.32/0.86  % (12605)------------------------------
% 3.32/0.86  % (12605)------------------------------
% 4.05/0.92  % (12610)Time limit reached!
% 4.05/0.92  % (12610)------------------------------
% 4.05/0.92  % (12610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.92  % (12610)Termination reason: Time limit
% 4.05/0.92  % (12610)Termination phase: Saturation
% 4.05/0.92  
% 4.05/0.92  % (12610)Memory used [KB]: 15863
% 4.05/0.92  % (12610)Time elapsed: 0.500 s
% 4.05/0.92  % (12610)------------------------------
% 4.05/0.92  % (12610)------------------------------
% 4.05/0.92  % (12612)Time limit reached!
% 4.05/0.92  % (12612)------------------------------
% 4.05/0.92  % (12612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.92  % (12612)Termination reason: Time limit
% 4.05/0.92  % (12612)Termination phase: Saturation
% 4.05/0.92  
% 4.05/0.92  % (12612)Memory used [KB]: 9978
% 4.05/0.92  % (12612)Time elapsed: 0.500 s
% 4.05/0.92  % (12612)------------------------------
% 4.05/0.92  % (12612)------------------------------
% 4.05/0.92  % (12600)Time limit reached!
% 4.05/0.92  % (12600)------------------------------
% 4.05/0.92  % (12600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.92  % (12600)Termination reason: Time limit
% 4.05/0.92  
% 4.05/0.92  % (12600)Memory used [KB]: 4605
% 4.05/0.92  % (12600)Time elapsed: 0.502 s
% 4.05/0.92  % (12600)------------------------------
% 4.05/0.92  % (12600)------------------------------
% 4.27/0.94  % (12601)Time limit reached!
% 4.27/0.94  % (12601)------------------------------
% 4.27/0.94  % (12601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.94  % (12601)Termination reason: Time limit
% 4.27/0.94  
% 4.27/0.94  % (12601)Memory used [KB]: 8059
% 4.27/0.94  % (12601)Time elapsed: 0.516 s
% 4.27/0.94  % (12601)------------------------------
% 4.27/0.94  % (12601)------------------------------
% 4.27/1.00  % (12664)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.91/1.03  % (12628)Time limit reached!
% 4.91/1.03  % (12628)------------------------------
% 4.91/1.03  % (12628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.91/1.03  % (12607)Time limit reached!
% 4.91/1.03  % (12607)------------------------------
% 4.91/1.03  % (12607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.91/1.03  % (12607)Termination reason: Time limit
% 4.91/1.03  
% 4.91/1.03  % (12607)Memory used [KB]: 11385
% 4.91/1.03  % (12607)Time elapsed: 0.610 s
% 4.91/1.03  % (12607)------------------------------
% 4.91/1.03  % (12607)------------------------------
% 4.91/1.03  % (12628)Termination reason: Time limit
% 4.91/1.03  
% 4.91/1.03  % (12628)Memory used [KB]: 8443
% 4.91/1.03  % (12628)Time elapsed: 0.615 s
% 4.91/1.03  % (12628)------------------------------
% 4.91/1.03  % (12628)------------------------------
% 4.91/1.03  % (12666)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.91/1.04  % (12669)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.91/1.05  % (12616)Time limit reached!
% 4.91/1.05  % (12616)------------------------------
% 4.91/1.05  % (12616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.91/1.05  % (12616)Termination reason: Time limit
% 4.91/1.05  
% 4.91/1.05  % (12616)Memory used [KB]: 18677
% 4.91/1.05  % (12616)Time elapsed: 0.621 s
% 4.91/1.05  % (12616)------------------------------
% 4.91/1.05  % (12616)------------------------------
% 4.91/1.06  % (12665)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.91/1.08  % (12667)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.35/1.15  % (12713)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.35/1.15  % (12708)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.41/1.18  % (12702)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.68/1.21  % (12621)Time limit reached!
% 6.68/1.21  % (12621)------------------------------
% 6.68/1.21  % (12621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.68/1.21  % (12621)Termination reason: Time limit
% 6.68/1.21  % (12621)Termination phase: Saturation
% 6.68/1.21  
% 6.68/1.21  % (12621)Memory used [KB]: 8827
% 6.68/1.21  % (12621)Time elapsed: 0.800 s
% 6.68/1.21  % (12621)------------------------------
% 6.68/1.21  % (12621)------------------------------
% 7.47/1.37  % (12666)Time limit reached!
% 7.47/1.37  % (12666)------------------------------
% 7.47/1.37  % (12666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.47/1.38  % (12665)Time limit reached!
% 7.47/1.38  % (12665)------------------------------
% 7.47/1.38  % (12665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.47/1.38  % (12665)Termination reason: Time limit
% 7.47/1.38  
% 7.47/1.38  % (12665)Memory used [KB]: 8059
% 7.47/1.38  % (12665)Time elapsed: 0.410 s
% 7.47/1.38  % (12665)------------------------------
% 7.47/1.38  % (12665)------------------------------
% 7.47/1.38  % (12666)Termination reason: Time limit
% 7.47/1.38  
% 7.47/1.38  % (12666)Memory used [KB]: 15479
% 7.47/1.38  % (12666)Time elapsed: 0.407 s
% 7.47/1.38  % (12666)------------------------------
% 7.47/1.38  % (12666)------------------------------
% 7.47/1.38  % (12804)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 8.02/1.42  % (12602)Time limit reached!
% 8.02/1.42  % (12602)------------------------------
% 8.02/1.42  % (12602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.02/1.42  % (12602)Termination reason: Time limit
% 8.02/1.42  
% 8.02/1.42  % (12602)Memory used [KB]: 16886
% 8.02/1.42  % (12602)Time elapsed: 1.006 s
% 8.02/1.42  % (12602)------------------------------
% 8.02/1.42  % (12602)------------------------------
% 8.78/1.51  % (12846)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.98/1.51  % (12848)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.08/1.53  % (12702)Refutation found. Thanks to Tanya!
% 9.08/1.53  % SZS status Theorem for theBenchmark
% 9.08/1.55  % SZS output start Proof for theBenchmark
% 9.08/1.55  fof(f6239,plain,(
% 9.08/1.55    $false),
% 9.08/1.55    inference(avatar_sat_refutation,[],[f198,f750,f1928,f5262,f6188,f6233])).
% 9.08/1.55  fof(f6233,plain,(
% 9.08/1.55    ~spl3_1 | spl3_2 | ~spl3_3),
% 9.08/1.55    inference(avatar_contradiction_clause,[],[f6232])).
% 9.08/1.55  fof(f6232,plain,(
% 9.08/1.55    $false | (~spl3_1 | spl3_2 | ~spl3_3)),
% 9.08/1.55    inference(subsumption_resolution,[],[f6231,f196])).
% 9.08/1.55  fof(f196,plain,(
% 9.08/1.55    ~r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | spl3_2),
% 9.08/1.55    inference(avatar_component_clause,[],[f195])).
% 9.08/1.55  fof(f195,plain,(
% 9.08/1.55    spl3_2 <=> r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))),
% 9.08/1.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 9.08/1.55  fof(f6231,plain,(
% 9.08/1.55    r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | (~spl3_1 | ~spl3_3)),
% 9.08/1.55    inference(forward_demodulation,[],[f6225,f58])).
% 9.08/1.55  fof(f58,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 9.08/1.55    inference(definition_unfolding,[],[f42,f40])).
% 9.08/1.55  fof(f40,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 9.08/1.55    inference(cnf_transformation,[],[f11])).
% 9.08/1.55  fof(f11,axiom,(
% 9.08/1.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 9.08/1.55  fof(f42,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 9.08/1.55    inference(cnf_transformation,[],[f13])).
% 9.08/1.55  fof(f13,axiom,(
% 9.08/1.55    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 9.08/1.55  fof(f6225,plain,(
% 9.08/1.55    r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | (~spl3_1 | ~spl3_3)),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f193,f749,f50])).
% 9.08/1.55  fof(f50,plain,(
% 9.08/1.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 9.08/1.55    inference(cnf_transformation,[],[f26])).
% 9.08/1.55  fof(f26,plain,(
% 9.08/1.55    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 9.08/1.55    inference(flattening,[],[f25])).
% 9.08/1.55  fof(f25,plain,(
% 9.08/1.55    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 9.08/1.55    inference(ennf_transformation,[],[f15])).
% 9.08/1.55  fof(f15,axiom,(
% 9.08/1.55    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 9.08/1.55  fof(f749,plain,(
% 9.08/1.55    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_3),
% 9.08/1.55    inference(avatar_component_clause,[],[f747])).
% 9.08/1.55  fof(f747,plain,(
% 9.08/1.55    spl3_3 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 9.08/1.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 9.08/1.55  fof(f193,plain,(
% 9.08/1.55    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_1),
% 9.08/1.55    inference(avatar_component_clause,[],[f191])).
% 9.08/1.55  fof(f191,plain,(
% 9.08/1.55    spl3_1 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 9.08/1.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 9.08/1.55  fof(f6188,plain,(
% 9.08/1.55    ~spl3_2 | spl3_3),
% 9.08/1.55    inference(avatar_contradiction_clause,[],[f6187])).
% 9.08/1.55  fof(f6187,plain,(
% 9.08/1.55    $false | (~spl3_2 | spl3_3)),
% 9.08/1.55    inference(subsumption_resolution,[],[f6181,f197])).
% 9.08/1.55  fof(f197,plain,(
% 9.08/1.55    r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | ~spl3_2),
% 9.08/1.55    inference(avatar_component_clause,[],[f195])).
% 9.08/1.55  fof(f6181,plain,(
% 9.08/1.55    ~r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | spl3_3),
% 9.08/1.55    inference(superposition,[],[f5270,f58])).
% 9.08/1.55  fof(f5270,plain,(
% 9.08/1.55    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ) | spl3_3),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f748,f440])).
% 9.08/1.55  fof(f440,plain,(
% 9.08/1.55    ( ! [X8,X7,X9] : (~r1_tarski(X9,k4_xboole_0(X8,X7)) | r1_xboole_0(X9,X7)) )),
% 9.08/1.55    inference(superposition,[],[f49,f326])).
% 9.08/1.55  fof(f326,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 9.08/1.55    inference(subsumption_resolution,[],[f314,f236])).
% 9.08/1.55  fof(f236,plain,(
% 9.08/1.55    ( ! [X0,X1] : (~r2_xboole_0(X0,k4_xboole_0(X0,X1)) | k4_xboole_0(X0,X1) = X0) )),
% 9.08/1.55    inference(resolution,[],[f186,f43])).
% 9.08/1.55  fof(f43,plain,(
% 9.08/1.55    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 9.08/1.55    inference(cnf_transformation,[],[f20])).
% 9.08/1.55  fof(f20,plain,(
% 9.08/1.55    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 9.08/1.55    inference(ennf_transformation,[],[f1])).
% 9.08/1.55  fof(f1,axiom,(
% 9.08/1.55    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 9.08/1.55  fof(f186,plain,(
% 9.08/1.55    ( ! [X0,X1] : (r2_xboole_0(k4_xboole_0(X0,X1),X0) | k4_xboole_0(X0,X1) = X0) )),
% 9.08/1.55    inference(resolution,[],[f45,f36])).
% 9.08/1.55  fof(f36,plain,(
% 9.08/1.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 9.08/1.55    inference(cnf_transformation,[],[f8])).
% 9.08/1.55  fof(f8,axiom,(
% 9.08/1.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 9.08/1.55  fof(f45,plain,(
% 9.08/1.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 9.08/1.55    inference(cnf_transformation,[],[f23])).
% 9.08/1.55  fof(f23,plain,(
% 9.08/1.55    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 9.08/1.55    inference(flattening,[],[f22])).
% 9.08/1.55  fof(f22,plain,(
% 9.08/1.55    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 9.08/1.55    inference(ennf_transformation,[],[f18])).
% 9.08/1.55  fof(f18,plain,(
% 9.08/1.55    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 9.08/1.55    inference(unused_predicate_definition_removal,[],[f3])).
% 9.08/1.55  fof(f3,axiom,(
% 9.08/1.55    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 9.08/1.55  fof(f314,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 | r2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 9.08/1.55    inference(resolution,[],[f263,f45])).
% 9.08/1.55  fof(f263,plain,(
% 9.08/1.55    ( ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f65,f134,f50])).
% 9.08/1.55  fof(f134,plain,(
% 9.08/1.55    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f65,f49])).
% 9.08/1.55  fof(f65,plain,(
% 9.08/1.55    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 9.08/1.55    inference(superposition,[],[f36,f60])).
% 9.08/1.55  fof(f60,plain,(
% 9.08/1.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 9.08/1.55    inference(forward_demodulation,[],[f57,f37])).
% 9.08/1.55  fof(f37,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 9.08/1.55    inference(cnf_transformation,[],[f10])).
% 9.08/1.55  fof(f10,axiom,(
% 9.08/1.55    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 9.08/1.55  fof(f57,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 9.08/1.55    inference(definition_unfolding,[],[f39,f40])).
% 9.08/1.55  fof(f39,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 9.08/1.55    inference(cnf_transformation,[],[f6])).
% 9.08/1.55  fof(f6,axiom,(
% 9.08/1.55    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 9.08/1.55  fof(f49,plain,(
% 9.08/1.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 9.08/1.55    inference(cnf_transformation,[],[f24])).
% 9.08/1.55  fof(f24,plain,(
% 9.08/1.55    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 9.08/1.55    inference(ennf_transformation,[],[f14])).
% 9.08/1.55  fof(f14,axiom,(
% 9.08/1.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 9.08/1.55  fof(f748,plain,(
% 9.08/1.55    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_3),
% 9.08/1.55    inference(avatar_component_clause,[],[f747])).
% 9.08/1.55  fof(f5262,plain,(
% 9.08/1.55    spl3_1 | ~spl3_2),
% 9.08/1.55    inference(avatar_contradiction_clause,[],[f5261])).
% 9.08/1.55  fof(f5261,plain,(
% 9.08/1.55    $false | (spl3_1 | ~spl3_2)),
% 9.08/1.55    inference(subsumption_resolution,[],[f5210,f2053])).
% 9.08/1.55  fof(f2053,plain,(
% 9.08/1.55    ( ! [X85,X83,X84] : (r1_xboole_0(k4_xboole_0(X85,k2_xboole_0(X83,X84)),k2_xboole_0(k4_xboole_0(X83,X84),k4_xboole_0(X84,X83)))) )),
% 9.08/1.55    inference(superposition,[],[f943,f58])).
% 9.08/1.55  fof(f943,plain,(
% 9.08/1.55    ( ! [X6,X4,X5] : (r1_xboole_0(k4_xboole_0(X6,X4),k4_xboole_0(X4,X5))) )),
% 9.08/1.55    inference(superposition,[],[f907,f68])).
% 9.08/1.55  fof(f68,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f36,f44])).
% 9.08/1.55  fof(f44,plain,(
% 9.08/1.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 9.08/1.55    inference(cnf_transformation,[],[f21])).
% 9.08/1.55  fof(f21,plain,(
% 9.08/1.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 9.08/1.55    inference(ennf_transformation,[],[f5])).
% 9.08/1.55  fof(f5,axiom,(
% 9.08/1.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 9.08/1.55  fof(f907,plain,(
% 9.08/1.55    ( ! [X50,X51,X49] : (r1_xboole_0(k4_xboole_0(X50,k2_xboole_0(X49,X51)),X49)) )),
% 9.08/1.55    inference(superposition,[],[f134,f722])).
% 9.08/1.55  fof(f722,plain,(
% 9.08/1.55    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X5))) = X3) )),
% 9.08/1.55    inference(subsumption_resolution,[],[f706,f236])).
% 9.08/1.55  fof(f706,plain,(
% 9.08/1.55    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X5))) = X3 | r2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X5))))) )),
% 9.08/1.55    inference(resolution,[],[f268,f45])).
% 9.08/1.55  fof(f268,plain,(
% 9.08/1.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))))) )),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f65,f136,f50])).
% 9.08/1.55  fof(f136,plain,(
% 9.08/1.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f92,f49])).
% 9.08/1.55  fof(f92,plain,(
% 9.08/1.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f37,f46])).
% 9.08/1.55  fof(f46,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 9.08/1.55    inference(cnf_transformation,[],[f31])).
% 9.08/1.55  fof(f31,plain,(
% 9.08/1.55    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 9.08/1.55    inference(nnf_transformation,[],[f9])).
% 9.08/1.55  fof(f9,axiom,(
% 9.08/1.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 9.08/1.55  fof(f5210,plain,(
% 9.08/1.55    ~r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | (spl3_1 | ~spl3_2)),
% 9.08/1.55    inference(superposition,[],[f2134,f205])).
% 9.08/1.55  fof(f205,plain,(
% 9.08/1.55    k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)) = k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | ~spl3_2),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f197,f44])).
% 9.08/1.55  fof(f2134,plain,(
% 9.08/1.55    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK0,X0))) ) | spl3_1),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f936,f1947,f50])).
% 9.08/1.55  fof(f1947,plain,(
% 9.08/1.55    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(sK0,X1)))) ) | spl3_1),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f921,f1937,f294])).
% 9.08/1.55  fof(f294,plain,(
% 9.08/1.55    ( ! [X2,X3] : (~r1_xboole_0(X3,X2) | r1_tarski(X3,k1_xboole_0) | ~r1_tarski(X3,X2)) )),
% 9.08/1.55    inference(superposition,[],[f50,f61])).
% 9.08/1.55  fof(f61,plain,(
% 9.08/1.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 9.08/1.55    inference(backward_demodulation,[],[f55,f60])).
% 9.08/1.55  fof(f55,plain,(
% 9.08/1.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 9.08/1.55    inference(definition_unfolding,[],[f35,f40])).
% 9.08/1.55  fof(f35,plain,(
% 9.08/1.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 9.08/1.55    inference(cnf_transformation,[],[f7])).
% 9.08/1.55  fof(f7,axiom,(
% 9.08/1.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 9.08/1.55  fof(f1937,plain,(
% 9.08/1.55    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) | spl3_1),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f1929,f1931,f45])).
% 9.08/1.55  fof(f1931,plain,(
% 9.08/1.55    ~r2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) | spl3_1),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f1929,f199])).
% 9.08/1.55  fof(f199,plain,(
% 9.08/1.55    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 9.08/1.55    inference(resolution,[],[f188,f43])).
% 9.08/1.55  fof(f188,plain,(
% 9.08/1.55    ( ! [X3] : (r2_xboole_0(k1_xboole_0,X3) | k1_xboole_0 = X3) )),
% 9.08/1.55    inference(resolution,[],[f45,f66])).
% 9.08/1.55  fof(f66,plain,(
% 9.08/1.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 9.08/1.55    inference(superposition,[],[f36,f61])).
% 9.08/1.55  fof(f1929,plain,(
% 9.08/1.55    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_1),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f192,f46])).
% 9.08/1.55  fof(f192,plain,(
% 9.08/1.55    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | spl3_1),
% 9.08/1.55    inference(avatar_component_clause,[],[f191])).
% 9.08/1.55  fof(f921,plain,(
% 9.08/1.55    ( ! [X97,X95,X98,X96] : (r1_xboole_0(k4_xboole_0(X95,X98),k4_xboole_0(X96,k2_xboole_0(X95,X97)))) )),
% 9.08/1.55    inference(superposition,[],[f445,f722])).
% 9.08/1.55  fof(f445,plain,(
% 9.08/1.55    ( ! [X26,X24,X25] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(X25,X24),X26),X24)) )),
% 9.08/1.55    inference(superposition,[],[f133,f326])).
% 9.08/1.55  fof(f133,plain,(
% 9.08/1.55    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0))) )),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f36,f49])).
% 9.08/1.55  fof(f936,plain,(
% 9.08/1.55    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 9.08/1.55    inference(unit_resulting_resolution,[],[f36,f907,f50])).
% 9.08/1.55  fof(f1928,plain,(
% 9.08/1.55    ~spl3_1 | ~spl3_3 | ~spl3_2),
% 9.08/1.55    inference(avatar_split_clause,[],[f64,f195,f747,f191])).
% 9.08/1.55  fof(f64,plain,(
% 9.08/1.55    ~r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 9.08/1.55    inference(backward_demodulation,[],[f52,f58])).
% 9.08/1.55  fof(f52,plain,(
% 9.08/1.55    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 9.08/1.55    inference(definition_unfolding,[],[f34,f40,f51])).
% 9.08/1.55  fof(f51,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 9.08/1.55    inference(definition_unfolding,[],[f41,f40])).
% 9.08/1.55  fof(f41,plain,(
% 9.08/1.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 9.08/1.55    inference(cnf_transformation,[],[f4])).
% 9.08/1.55  fof(f4,axiom,(
% 9.08/1.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 9.08/1.55  fof(f34,plain,(
% 9.08/1.55    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 9.08/1.55    inference(cnf_transformation,[],[f30])).
% 9.08/1.55  fof(f30,plain,(
% 9.08/1.55    (~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2)))),
% 9.08/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).
% 9.08/1.55  fof(f29,plain,(
% 9.08/1.55    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2)))) => ((~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))))),
% 9.08/1.55    introduced(choice_axiom,[])).
% 9.08/1.55  fof(f28,plain,(
% 9.08/1.55    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 9.08/1.55    inference(flattening,[],[f27])).
% 9.08/1.55  fof(f27,plain,(
% 9.08/1.55    ? [X0,X1,X2] : (((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 9.08/1.55    inference(nnf_transformation,[],[f19])).
% 9.08/1.55  fof(f19,plain,(
% 9.08/1.55    ? [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <~> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 9.08/1.55    inference(ennf_transformation,[],[f17])).
% 9.08/1.55  fof(f17,negated_conjecture,(
% 9.08/1.55    ~! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 9.08/1.55    inference(negated_conjecture,[],[f16])).
% 9.08/1.55  fof(f16,conjecture,(
% 9.08/1.55    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 9.08/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 9.08/1.55  fof(f750,plain,(
% 9.08/1.55    spl3_3 | spl3_2),
% 9.08/1.55    inference(avatar_split_clause,[],[f63,f195,f747])).
% 9.08/1.55  fof(f63,plain,(
% 9.08/1.55    r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 9.08/1.55    inference(backward_demodulation,[],[f53,f58])).
% 9.08/1.55  fof(f53,plain,(
% 9.08/1.55    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 9.08/1.55    inference(definition_unfolding,[],[f33,f40,f51])).
% 9.08/1.55  fof(f33,plain,(
% 9.08/1.55    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 9.08/1.55    inference(cnf_transformation,[],[f30])).
% 9.08/1.55  fof(f198,plain,(
% 9.08/1.55    spl3_1 | spl3_2),
% 9.08/1.55    inference(avatar_split_clause,[],[f62,f195,f191])).
% 9.08/1.55  fof(f62,plain,(
% 9.08/1.55    r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 9.08/1.55    inference(backward_demodulation,[],[f54,f58])).
% 9.08/1.55  fof(f54,plain,(
% 9.08/1.55    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 9.08/1.55    inference(definition_unfolding,[],[f32,f51])).
% 9.08/1.55  fof(f32,plain,(
% 9.08/1.55    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 9.08/1.55    inference(cnf_transformation,[],[f30])).
% 9.08/1.55  % SZS output end Proof for theBenchmark
% 9.08/1.55  % (12702)------------------------------
% 9.08/1.55  % (12702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.08/1.55  % (12702)Termination reason: Refutation
% 9.08/1.55  
% 9.08/1.55  % (12702)Memory used [KB]: 8955
% 9.08/1.55  % (12702)Time elapsed: 0.485 s
% 9.08/1.55  % (12702)------------------------------
% 9.08/1.55  % (12702)------------------------------
% 9.08/1.55  % (12599)Success in time 1.187 s
%------------------------------------------------------------------------------
