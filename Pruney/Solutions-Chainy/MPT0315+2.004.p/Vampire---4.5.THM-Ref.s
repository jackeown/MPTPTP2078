%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:10 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 175 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  180 ( 401 expanded)
%              Number of equality atoms :   62 ( 134 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1635,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f1262,f1634])).

fof(f1634,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f1614])).

fof(f1614,plain,
    ( $false
    | ~ spl4_1 ),
    inference(resolution,[],[f1604,f22])).

fof(f22,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    & ( r1_xboole_0(sK2,sK3)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) ) )
   => ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
      & ( r1_xboole_0(sK2,sK3)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f1604,plain,
    ( ! [X21,X20] : r1_xboole_0(k2_zfmisc_1(sK0,X20),k2_zfmisc_1(sK1,X21))
    | ~ spl4_1 ),
    inference(resolution,[],[f1576,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1576,plain,
    ( ! [X2,X1] : r1_xboole_0(k2_zfmisc_1(sK1,X1),k2_zfmisc_1(sK0,X2))
    | ~ spl4_1 ),
    inference(resolution,[],[f1414,f204])).

fof(f204,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r1_xboole_0(X19,k2_zfmisc_1(X16,k2_xboole_0(X17,X18)))
      | r1_xboole_0(X19,k2_zfmisc_1(X16,X18)) ) ),
    inference(superposition,[],[f39,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1414,plain,
    ( ! [X23,X22] : r1_xboole_0(k2_zfmisc_1(sK1,X22),k2_zfmisc_1(sK0,k2_xboole_0(X22,X23)))
    | ~ spl4_1 ),
    inference(resolution,[],[f1298,f25])).

fof(f1298,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(X0,X1)),k2_zfmisc_1(sK1,X0))
    | ~ spl4_1 ),
    inference(resolution,[],[f1283,f205])).

fof(f205,plain,(
    ! [X23,X21,X22,X20] :
      ( ~ r1_xboole_0(X23,k2_zfmisc_1(X20,k2_xboole_0(X21,X22)))
      | r1_xboole_0(X23,k2_zfmisc_1(X20,X21)) ) ),
    inference(superposition,[],[f38,f34])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1283,plain,
    ( ! [X0] : r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X0))
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f1282])).

fof(f1282,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X0)) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1281,f46])).

fof(f46,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1281,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X0)) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1276,f120])).

fof(f120,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f40,f118])).

fof(f118,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(resolution,[],[f75,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f75,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f41,f40])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f1276,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(sK0,sK0),X0)
        | r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X0)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f427,f1267])).

fof(f1267,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f50,f26])).

fof(f50,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f427,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X4)),X3)
      | r1_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X3)) ) ),
    inference(superposition,[],[f41,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f35,f24,f24])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f1262,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f1236])).

fof(f1236,plain,
    ( $false
    | ~ spl4_2 ),
    inference(resolution,[],[f809,f343])).

fof(f343,plain,(
    ! [X12] : ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k2_xboole_0(X12,sK1),sK3)) ),
    inference(resolution,[],[f178,f22])).

fof(f178,plain,(
    ! [X14,X17,X15,X16] :
      ( r1_xboole_0(X17,k2_zfmisc_1(X16,X15))
      | ~ r1_xboole_0(X17,k2_zfmisc_1(k2_xboole_0(X14,X16),X15)) ) ),
    inference(superposition,[],[f39,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f809,plain,
    ( ! [X14,X13] : r1_xboole_0(k2_zfmisc_1(X13,sK2),k2_zfmisc_1(k2_xboole_0(X13,X14),sK3))
    | ~ spl4_2 ),
    inference(resolution,[],[f765,f25])).

fof(f765,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(k2_xboole_0(X0,X1),sK3),k2_zfmisc_1(X0,sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f734,f179])).

fof(f179,plain,(
    ! [X21,X19,X20,X18] :
      ( ~ r1_xboole_0(X21,k2_zfmisc_1(k2_xboole_0(X18,X20),X19))
      | r1_xboole_0(X21,k2_zfmisc_1(X18,X19)) ) ),
    inference(superposition,[],[f38,f33])).

fof(f734,plain,
    ( ! [X22] : r1_xboole_0(k2_zfmisc_1(X22,sK3),k2_zfmisc_1(X22,sK2))
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f733])).

fof(f733,plain,
    ( ! [X22] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k2_zfmisc_1(X22,sK3),k2_zfmisc_1(X22,sK2)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f732,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f732,plain,
    ( ! [X22] :
        ( k1_xboole_0 != k2_zfmisc_1(X22,k1_xboole_0)
        | r1_xboole_0(k2_zfmisc_1(X22,sK3),k2_zfmisc_1(X22,sK2)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f692,f82])).

fof(f82,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK3)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f79,f59])).

fof(f59,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f26,f56])).

fof(f56,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f25,f54])).

fof(f54,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_2
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f79,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f42,f56])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f692,plain,
    ( ! [X22] :
        ( k1_xboole_0 != k2_zfmisc_1(X22,k4_xboole_0(sK3,sK3))
        | r1_xboole_0(k2_zfmisc_1(X22,sK3),k2_zfmisc_1(X22,sK2)) )
    | ~ spl4_2 ),
    inference(superposition,[],[f374,f59])).

fof(f374,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) ) ),
    inference(superposition,[],[f41,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f36,f24,f24])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f21,f52,f48])).

fof(f21,plain,
    ( r1_xboole_0(sK2,sK3)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (915)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (926)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (910)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (904)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (901)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (899)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (901)Refutation not found, incomplete strategy% (901)------------------------------
% 0.21/0.54  % (901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (901)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (901)Memory used [KB]: 10618
% 0.21/0.54  % (901)Time elapsed: 0.122 s
% 0.21/0.54  % (901)------------------------------
% 0.21/0.54  % (901)------------------------------
% 0.21/0.54  % (899)Refutation not found, incomplete strategy% (899)------------------------------
% 0.21/0.54  % (899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (899)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (899)Memory used [KB]: 1663
% 0.21/0.54  % (899)Time elapsed: 0.122 s
% 0.21/0.54  % (899)------------------------------
% 0.21/0.54  % (899)------------------------------
% 0.21/0.54  % (900)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (924)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (903)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (934)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (913)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (902)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.55  % (916)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (911)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.55  % (916)Refutation not found, incomplete strategy% (916)------------------------------
% 1.38/0.55  % (916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (916)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (916)Memory used [KB]: 10618
% 1.38/0.55  % (916)Time elapsed: 0.136 s
% 1.38/0.55  % (916)------------------------------
% 1.38/0.55  % (916)------------------------------
% 1.38/0.55  % (923)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (924)Refutation not found, incomplete strategy% (924)------------------------------
% 1.38/0.55  % (924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (924)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (924)Memory used [KB]: 10746
% 1.38/0.55  % (924)Time elapsed: 0.100 s
% 1.38/0.55  % (924)------------------------------
% 1.38/0.55  % (924)------------------------------
% 1.38/0.55  % (909)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.55  % (909)Refutation not found, incomplete strategy% (909)------------------------------
% 1.38/0.55  % (909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (909)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (909)Memory used [KB]: 10618
% 1.38/0.55  % (909)Time elapsed: 0.138 s
% 1.38/0.55  % (909)------------------------------
% 1.38/0.55  % (909)------------------------------
% 1.38/0.56  % (925)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.56  % (908)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.56  % (905)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.56  % (908)Refutation not found, incomplete strategy% (908)------------------------------
% 1.38/0.56  % (908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (908)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (908)Memory used [KB]: 10618
% 1.38/0.56  % (908)Time elapsed: 0.147 s
% 1.38/0.56  % (908)------------------------------
% 1.38/0.56  % (908)------------------------------
% 1.38/0.56  % (906)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.56  % (919)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.56  % (930)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.56  % (928)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.56  % (929)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.56  % (914)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.56  % (912)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.57  % (922)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.57  % (907)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.57  % (921)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.57  % (907)Refutation not found, incomplete strategy% (907)------------------------------
% 1.38/0.57  % (907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (907)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (907)Memory used [KB]: 10746
% 1.38/0.57  % (907)Time elapsed: 0.159 s
% 1.38/0.57  % (907)------------------------------
% 1.38/0.57  % (907)------------------------------
% 1.38/0.57  % (927)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.00/0.66  % (1000)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.00/0.66  % (911)Refutation found. Thanks to Tanya!
% 2.00/0.66  % SZS status Theorem for theBenchmark
% 2.00/0.66  % SZS output start Proof for theBenchmark
% 2.00/0.66  fof(f1635,plain,(
% 2.00/0.66    $false),
% 2.00/0.66    inference(avatar_sat_refutation,[],[f55,f1262,f1634])).
% 2.00/0.66  fof(f1634,plain,(
% 2.00/0.66    ~spl4_1),
% 2.00/0.66    inference(avatar_contradiction_clause,[],[f1614])).
% 2.00/0.66  fof(f1614,plain,(
% 2.00/0.66    $false | ~spl4_1),
% 2.00/0.66    inference(resolution,[],[f1604,f22])).
% 2.00/0.66  fof(f22,plain,(
% 2.00/0.66    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 2.00/0.66    inference(cnf_transformation,[],[f16])).
% 2.00/0.66  fof(f16,plain,(
% 2.00/0.66    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) & (r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1))),
% 2.00/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15])).
% 2.00/0.66  fof(f15,plain,(
% 2.00/0.66    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1))) => (~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) & (r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f12,plain,(
% 2.00/0.66    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)))),
% 2.00/0.66    inference(ennf_transformation,[],[f11])).
% 2.00/0.66  fof(f11,negated_conjecture,(
% 2.00/0.66    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 2.00/0.66    inference(negated_conjecture,[],[f10])).
% 2.00/0.66  fof(f10,conjecture,(
% 2.00/0.66    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 2.00/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 2.00/0.66  fof(f1604,plain,(
% 2.00/0.66    ( ! [X21,X20] : (r1_xboole_0(k2_zfmisc_1(sK0,X20),k2_zfmisc_1(sK1,X21))) ) | ~spl4_1),
% 2.00/0.66    inference(resolution,[],[f1576,f25])).
% 2.00/0.66  fof(f25,plain,(
% 2.00/0.66    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f13])).
% 2.00/0.66  fof(f13,plain,(
% 2.00/0.66    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.00/0.66    inference(ennf_transformation,[],[f2])).
% 2.00/0.66  fof(f2,axiom,(
% 2.00/0.66    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.00/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.00/0.66  fof(f1576,plain,(
% 2.00/0.66    ( ! [X2,X1] : (r1_xboole_0(k2_zfmisc_1(sK1,X1),k2_zfmisc_1(sK0,X2))) ) | ~spl4_1),
% 2.00/0.66    inference(resolution,[],[f1414,f204])).
% 2.00/0.66  fof(f204,plain,(
% 2.00/0.66    ( ! [X19,X17,X18,X16] : (~r1_xboole_0(X19,k2_zfmisc_1(X16,k2_xboole_0(X17,X18))) | r1_xboole_0(X19,k2_zfmisc_1(X16,X18))) )),
% 2.00/0.66    inference(superposition,[],[f39,f34])).
% 2.00/0.66  fof(f34,plain,(
% 2.00/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.00/0.66    inference(cnf_transformation,[],[f8])).
% 2.00/0.66  fof(f8,axiom,(
% 2.00/0.66    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.00/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 2.08/0.66  fof(f39,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f14])).
% 2.08/0.66  fof(f14,plain,(
% 2.08/0.66    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.08/0.66    inference(ennf_transformation,[],[f5])).
% 2.08/0.66  fof(f5,axiom,(
% 2.08/0.66    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.08/0.66  fof(f1414,plain,(
% 2.08/0.66    ( ! [X23,X22] : (r1_xboole_0(k2_zfmisc_1(sK1,X22),k2_zfmisc_1(sK0,k2_xboole_0(X22,X23)))) ) | ~spl4_1),
% 2.08/0.66    inference(resolution,[],[f1298,f25])).
% 2.08/0.66  fof(f1298,plain,(
% 2.08/0.66    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(X0,X1)),k2_zfmisc_1(sK1,X0))) ) | ~spl4_1),
% 2.08/0.66    inference(resolution,[],[f1283,f205])).
% 2.08/0.66  fof(f205,plain,(
% 2.08/0.66    ( ! [X23,X21,X22,X20] : (~r1_xboole_0(X23,k2_zfmisc_1(X20,k2_xboole_0(X21,X22))) | r1_xboole_0(X23,k2_zfmisc_1(X20,X21))) )),
% 2.08/0.66    inference(superposition,[],[f38,f34])).
% 2.08/0.66  fof(f38,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f14])).
% 2.08/0.66  fof(f1283,plain,(
% 2.08/0.66    ( ! [X0] : (r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X0))) ) | ~spl4_1),
% 2.08/0.66    inference(trivial_inequality_removal,[],[f1282])).
% 2.08/0.66  fof(f1282,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X0))) ) | ~spl4_1),
% 2.08/0.66    inference(forward_demodulation,[],[f1281,f46])).
% 2.08/0.66  fof(f46,plain,(
% 2.08/0.66    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.08/0.66    inference(equality_resolution,[],[f31])).
% 2.08/0.66  fof(f31,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.08/0.66    inference(cnf_transformation,[],[f20])).
% 2.08/0.66  fof(f20,plain,(
% 2.08/0.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.08/0.66    inference(flattening,[],[f19])).
% 2.08/0.66  fof(f19,plain,(
% 2.08/0.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.08/0.66    inference(nnf_transformation,[],[f7])).
% 2.08/0.66  fof(f7,axiom,(
% 2.08/0.66    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.08/0.66  fof(f1281,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X0))) ) | ~spl4_1),
% 2.08/0.66    inference(forward_demodulation,[],[f1276,f120])).
% 2.08/0.66  fof(f120,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.08/0.66    inference(backward_demodulation,[],[f40,f118])).
% 2.08/0.66  fof(f118,plain,(
% 2.08/0.66    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.08/0.66    inference(resolution,[],[f75,f26])).
% 2.08/0.66  fof(f26,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.08/0.66    inference(cnf_transformation,[],[f17])).
% 2.08/0.66  fof(f17,plain,(
% 2.08/0.66    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.08/0.66    inference(nnf_transformation,[],[f6])).
% 2.08/0.66  fof(f6,axiom,(
% 2.08/0.66    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.08/0.66  fof(f75,plain,(
% 2.08/0.66    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.08/0.66    inference(trivial_inequality_removal,[],[f74])).
% 2.08/0.66  fof(f74,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 2.08/0.66    inference(superposition,[],[f41,f40])).
% 2.08/0.66  fof(f41,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.08/0.66    inference(definition_unfolding,[],[f29,f24])).
% 2.08/0.66  fof(f24,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f4])).
% 2.08/0.66  fof(f4,axiom,(
% 2.08/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.08/0.66  fof(f29,plain,(
% 2.08/0.66    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.08/0.66    inference(cnf_transformation,[],[f18])).
% 2.08/0.66  fof(f18,plain,(
% 2.08/0.66    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.08/0.66    inference(nnf_transformation,[],[f1])).
% 2.08/0.66  fof(f1,axiom,(
% 2.08/0.66    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.08/0.66  fof(f40,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.08/0.66    inference(definition_unfolding,[],[f23,f24])).
% 2.08/0.66  fof(f23,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f3])).
% 2.08/0.66  fof(f3,axiom,(
% 2.08/0.66    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.08/0.66  fof(f1276,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(sK0,sK0),X0) | r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X0))) ) | ~spl4_1),
% 2.08/0.66    inference(superposition,[],[f427,f1267])).
% 2.08/0.66  fof(f1267,plain,(
% 2.08/0.66    sK0 = k4_xboole_0(sK0,sK1) | ~spl4_1),
% 2.08/0.66    inference(resolution,[],[f50,f26])).
% 2.08/0.66  fof(f50,plain,(
% 2.08/0.66    r1_xboole_0(sK0,sK1) | ~spl4_1),
% 2.08/0.66    inference(avatar_component_clause,[],[f48])).
% 2.08/0.66  fof(f48,plain,(
% 2.08/0.66    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 2.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.08/0.66  fof(f427,plain,(
% 2.08/0.66    ( ! [X4,X2,X3] : (k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X4)),X3) | r1_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X3))) )),
% 2.08/0.66    inference(superposition,[],[f41,f44])).
% 2.08/0.66  fof(f44,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 2.08/0.66    inference(definition_unfolding,[],[f35,f24,f24])).
% 2.08/0.66  fof(f35,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f9])).
% 2.08/0.66  fof(f9,axiom,(
% 2.08/0.66    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 2.08/0.66  fof(f1262,plain,(
% 2.08/0.66    ~spl4_2),
% 2.08/0.66    inference(avatar_contradiction_clause,[],[f1236])).
% 2.08/0.66  fof(f1236,plain,(
% 2.08/0.66    $false | ~spl4_2),
% 2.08/0.66    inference(resolution,[],[f809,f343])).
% 2.08/0.66  fof(f343,plain,(
% 2.08/0.66    ( ! [X12] : (~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(k2_xboole_0(X12,sK1),sK3))) )),
% 2.08/0.66    inference(resolution,[],[f178,f22])).
% 2.08/0.66  fof(f178,plain,(
% 2.08/0.66    ( ! [X14,X17,X15,X16] : (r1_xboole_0(X17,k2_zfmisc_1(X16,X15)) | ~r1_xboole_0(X17,k2_zfmisc_1(k2_xboole_0(X14,X16),X15))) )),
% 2.08/0.66    inference(superposition,[],[f39,f33])).
% 2.08/0.66  fof(f33,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f8])).
% 2.08/0.66  fof(f809,plain,(
% 2.08/0.66    ( ! [X14,X13] : (r1_xboole_0(k2_zfmisc_1(X13,sK2),k2_zfmisc_1(k2_xboole_0(X13,X14),sK3))) ) | ~spl4_2),
% 2.08/0.66    inference(resolution,[],[f765,f25])).
% 2.08/0.66  fof(f765,plain,(
% 2.08/0.66    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(k2_xboole_0(X0,X1),sK3),k2_zfmisc_1(X0,sK2))) ) | ~spl4_2),
% 2.08/0.66    inference(resolution,[],[f734,f179])).
% 2.08/0.66  fof(f179,plain,(
% 2.08/0.66    ( ! [X21,X19,X20,X18] : (~r1_xboole_0(X21,k2_zfmisc_1(k2_xboole_0(X18,X20),X19)) | r1_xboole_0(X21,k2_zfmisc_1(X18,X19))) )),
% 2.08/0.66    inference(superposition,[],[f38,f33])).
% 2.08/0.66  fof(f734,plain,(
% 2.08/0.66    ( ! [X22] : (r1_xboole_0(k2_zfmisc_1(X22,sK3),k2_zfmisc_1(X22,sK2))) ) | ~spl4_2),
% 2.08/0.66    inference(trivial_inequality_removal,[],[f733])).
% 2.08/0.66  fof(f733,plain,(
% 2.08/0.66    ( ! [X22] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(X22,sK3),k2_zfmisc_1(X22,sK2))) ) | ~spl4_2),
% 2.08/0.66    inference(forward_demodulation,[],[f732,f45])).
% 2.08/0.66  fof(f45,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.08/0.66    inference(equality_resolution,[],[f32])).
% 2.08/0.66  fof(f32,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.08/0.66    inference(cnf_transformation,[],[f20])).
% 2.08/0.66  fof(f732,plain,(
% 2.08/0.66    ( ! [X22] : (k1_xboole_0 != k2_zfmisc_1(X22,k1_xboole_0) | r1_xboole_0(k2_zfmisc_1(X22,sK3),k2_zfmisc_1(X22,sK2))) ) | ~spl4_2),
% 2.08/0.66    inference(forward_demodulation,[],[f692,f82])).
% 2.08/0.66  fof(f82,plain,(
% 2.08/0.66    k1_xboole_0 = k4_xboole_0(sK3,sK3) | ~spl4_2),
% 2.08/0.66    inference(forward_demodulation,[],[f79,f59])).
% 2.08/0.66  fof(f59,plain,(
% 2.08/0.66    sK3 = k4_xboole_0(sK3,sK2) | ~spl4_2),
% 2.08/0.66    inference(resolution,[],[f26,f56])).
% 2.08/0.66  fof(f56,plain,(
% 2.08/0.66    r1_xboole_0(sK3,sK2) | ~spl4_2),
% 2.08/0.66    inference(resolution,[],[f25,f54])).
% 2.08/0.66  fof(f54,plain,(
% 2.08/0.66    r1_xboole_0(sK2,sK3) | ~spl4_2),
% 2.08/0.66    inference(avatar_component_clause,[],[f52])).
% 2.08/0.66  fof(f52,plain,(
% 2.08/0.66    spl4_2 <=> r1_xboole_0(sK2,sK3)),
% 2.08/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.08/0.66  fof(f79,plain,(
% 2.08/0.66    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) | ~spl4_2),
% 2.08/0.66    inference(resolution,[],[f42,f56])).
% 2.08/0.66  fof(f42,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.08/0.66    inference(definition_unfolding,[],[f28,f24])).
% 2.08/0.66  fof(f28,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f18])).
% 2.08/0.66  fof(f692,plain,(
% 2.08/0.66    ( ! [X22] : (k1_xboole_0 != k2_zfmisc_1(X22,k4_xboole_0(sK3,sK3)) | r1_xboole_0(k2_zfmisc_1(X22,sK3),k2_zfmisc_1(X22,sK2))) ) | ~spl4_2),
% 2.08/0.66    inference(superposition,[],[f374,f59])).
% 2.08/0.66  fof(f374,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) )),
% 2.08/0.66    inference(superposition,[],[f41,f43])).
% 2.08/0.66  fof(f43,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 2.08/0.66    inference(definition_unfolding,[],[f36,f24,f24])).
% 2.08/0.66  fof(f36,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f9])).
% 2.08/0.66  fof(f55,plain,(
% 2.08/0.66    spl4_1 | spl4_2),
% 2.08/0.66    inference(avatar_split_clause,[],[f21,f52,f48])).
% 2.08/0.66  fof(f21,plain,(
% 2.08/0.66    r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)),
% 2.08/0.66    inference(cnf_transformation,[],[f16])).
% 2.08/0.66  % SZS output end Proof for theBenchmark
% 2.08/0.66  % (911)------------------------------
% 2.08/0.66  % (911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.66  % (911)Termination reason: Refutation
% 2.08/0.66  
% 2.08/0.66  % (911)Memory used [KB]: 7419
% 2.08/0.66  % (911)Time elapsed: 0.246 s
% 2.08/0.66  % (911)------------------------------
% 2.08/0.66  % (911)------------------------------
% 2.08/0.66  % (898)Success in time 0.286 s
%------------------------------------------------------------------------------
