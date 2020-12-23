%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:07 EST 2020

% Result     : Theorem 5.52s
% Output     : Refutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 319 expanded)
%              Number of leaves         :   40 ( 120 expanded)
%              Depth                    :   14
%              Number of atoms          :  478 ( 832 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1490,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f114,f119,f176,f182,f788,f808,f838,f968,f983,f1004,f1038,f1077,f1151,f1483])).

fof(f1483,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_53 ),
    inference(avatar_contradiction_clause,[],[f1482])).

fof(f1482,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_53 ),
    inference(subsumption_resolution,[],[f1481,f100])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1481,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_53 ),
    inference(subsumption_resolution,[],[f1475,f95])).

fof(f95,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1475,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_53 ),
    inference(resolution,[],[f978,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f978,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_53 ),
    inference(avatar_component_clause,[],[f976])).

fof(f976,plain,
    ( spl3_53
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f1151,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_58 ),
    inference(avatar_contradiction_clause,[],[f1150])).

fof(f1150,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_58 ),
    inference(subsumption_resolution,[],[f1149,f100])).

fof(f1149,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_58 ),
    inference(subsumption_resolution,[],[f1148,f95])).

fof(f1148,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_58 ),
    inference(subsumption_resolution,[],[f1141,f85])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1141,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_58 ),
    inference(resolution,[],[f1037,f249])).

fof(f249,plain,(
    ! [X10,X8,X11,X9] :
      ( r1_tarski(X11,k4_subset_1(X10,X8,X9))
      | ~ r1_tarski(X11,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X10)) ) ),
    inference(superposition,[],[f80,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f79])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1037,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_58 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f1035,plain,
    ( spl3_58
  <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f1077,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_54 ),
    inference(avatar_contradiction_clause,[],[f1076])).

fof(f1076,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_54 ),
    inference(subsumption_resolution,[],[f1075,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1075,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_54 ),
    inference(forward_demodulation,[],[f1074,f544])).

fof(f544,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,X7) ),
    inference(subsumption_resolution,[],[f536,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f536,plain,(
    ! [X7] :
      ( k1_xboole_0 = k4_xboole_0(X7,X7)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)) ) ),
    inference(superposition,[],[f162,f512])).

fof(f512,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f504,f57])).

fof(f504,plain,(
    ! [X0] :
      ( k3_subset_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f222,f55])).

fof(f222,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k3_subset_1(X2,X3))
      | k3_subset_1(X2,X3) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f219,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f219,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k3_subset_1(X2,X3))
      | k3_subset_1(X2,X3) = X2
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f213,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f65,f56])).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(k3_subset_1(X0,X1),X1)
          | k2_subset_1(X0) != X1 )
        & ( k2_subset_1(X0) = X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f162,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,k3_subset_1(X2,X3)) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f158,f62])).

fof(f158,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,k3_subset_1(X2,X3)) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f64,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1074,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK1),sK2)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_54 ),
    inference(subsumption_resolution,[],[f1073,f100])).

fof(f1073,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK1),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_54 ),
    inference(subsumption_resolution,[],[f1068,f95])).

fof(f1068,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_54 ),
    inference(resolution,[],[f982,f248])).

fof(f248,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_tarski(X7,k4_subset_1(X6,X4,X5))
      | ~ r1_tarski(k4_xboole_0(X7,X4),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f81,f83])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f73,f79])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f982,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_54 ),
    inference(avatar_component_clause,[],[f980])).

fof(f980,plain,
    ( spl3_54
  <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f1038,plain,
    ( ~ spl3_53
    | ~ spl3_58
    | ~ spl3_2
    | ~ spl3_4
    | spl3_43 ),
    inference(avatar_split_clause,[],[f1033,f785,f103,f93,f1035,f976])).

fof(f103,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f785,plain,
    ( spl3_43
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1033,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_4
    | spl3_43 ),
    inference(subsumption_resolution,[],[f1032,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f1032,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | spl3_43 ),
    inference(subsumption_resolution,[],[f1028,f95])).

fof(f1028,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_43 ),
    inference(resolution,[],[f787,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f787,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f785])).

fof(f1004,plain,
    ( ~ spl3_5
    | ~ spl3_11
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f1003])).

fof(f1003,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_11
    | spl3_52 ),
    inference(subsumption_resolution,[],[f998,f175])).

fof(f175,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl3_11
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f998,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_5
    | spl3_52 ),
    inference(resolution,[],[f967,f145])).

fof(f145,plain,
    ( ! [X4] :
        ( r1_tarski(X4,u1_struct_0(sK0))
        | ~ r1_tarski(X4,sK2) )
    | ~ spl3_5 ),
    inference(resolution,[],[f75,f113])).

fof(f113,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_5
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f967,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f965])).

fof(f965,plain,
    ( spl3_52
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f983,plain,
    ( ~ spl3_53
    | ~ spl3_54
    | ~ spl3_3
    | ~ spl3_4
    | spl3_42 ),
    inference(avatar_split_clause,[],[f974,f781,f103,f98,f980,f976])).

fof(f781,plain,
    ( spl3_42
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f974,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_4
    | spl3_42 ),
    inference(subsumption_resolution,[],[f973,f105])).

fof(f973,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_42 ),
    inference(subsumption_resolution,[],[f969,f100])).

fof(f969,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_42 ),
    inference(resolution,[],[f783,f59])).

fof(f783,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f781])).

fof(f968,plain,
    ( ~ spl3_52
    | spl3_41 ),
    inference(avatar_split_clause,[],[f963,f777,f965])).

fof(f777,plain,
    ( spl3_41
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f963,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_41 ),
    inference(resolution,[],[f779,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f779,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_41 ),
    inference(avatar_component_clause,[],[f777])).

fof(f838,plain,
    ( ~ spl3_6
    | ~ spl3_12
    | spl3_46 ),
    inference(avatar_contradiction_clause,[],[f837])).

fof(f837,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_12
    | spl3_46 ),
    inference(subsumption_resolution,[],[f831,f181])).

fof(f181,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl3_12
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f831,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_6
    | spl3_46 ),
    inference(resolution,[],[f807,f146])).

fof(f146,plain,
    ( ! [X5] :
        ( r1_tarski(X5,u1_struct_0(sK0))
        | ~ r1_tarski(X5,sK1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f75,f118])).

fof(f118,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f807,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f805])).

fof(f805,plain,
    ( spl3_46
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f808,plain,
    ( ~ spl3_46
    | spl3_40 ),
    inference(avatar_split_clause,[],[f803,f773,f805])).

fof(f773,plain,
    ( spl3_40
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f803,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_40 ),
    inference(resolution,[],[f775,f71])).

fof(f775,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_40 ),
    inference(avatar_component_clause,[],[f773])).

fof(f788,plain,
    ( ~ spl3_40
    | ~ spl3_41
    | ~ spl3_42
    | ~ spl3_43
    | spl3_1 ),
    inference(avatar_split_clause,[],[f757,f88,f785,f781,f777,f773])).

fof(f88,plain,
    ( spl3_1
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f757,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(resolution,[],[f247,f90])).

fof(f90,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f247,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_subset_1(X2,X0,X1),X3)
      | ~ r1_tarski(X1,X3)
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f82,f83])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f182,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f177,f103,f98,f179])).

fof(f177,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f167,f105])).

fof(f167,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f58,f100])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f176,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f171,f103,f93,f173])).

fof(f171,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f166,f105])).

fof(f166,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f58,f95])).

fof(f119,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f108,f98,f116])).

fof(f108,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f70,f100])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f114,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f107,f93,f111])).

fof(f107,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f95])).

fof(f106,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f51,f103])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

fof(f101,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f52,f98])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f53,f93])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f88])).

fof(f54,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:28:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (32620)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.49  % (32628)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (32609)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (32626)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (32612)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (32607)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (32610)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (32608)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (32611)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (32629)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (32613)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (32625)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (32622)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (32624)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (32634)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (32636)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (32621)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (32614)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (32633)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (32618)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (32616)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (32615)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (32627)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (32617)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (32632)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (32630)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (32619)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (32635)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (32623)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.66/0.58  % (32631)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 3.33/0.85  % (32631)Time limit reached!
% 3.33/0.85  % (32631)------------------------------
% 3.33/0.85  % (32631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.85  % (32631)Termination reason: Time limit
% 3.33/0.85  % (32631)Termination phase: Saturation
% 3.33/0.85  
% 3.33/0.85  % (32631)Memory used [KB]: 12920
% 3.33/0.85  % (32631)Time elapsed: 0.400 s
% 3.33/0.85  % (32631)------------------------------
% 3.33/0.85  % (32631)------------------------------
% 3.88/0.86  % (32609)Time limit reached!
% 3.88/0.86  % (32609)------------------------------
% 3.88/0.86  % (32609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.87  % (32609)Termination reason: Time limit
% 3.93/0.87  
% 3.93/0.87  % (32609)Memory used [KB]: 6780
% 3.93/0.87  % (32609)Time elapsed: 0.445 s
% 3.93/0.87  % (32609)------------------------------
% 3.93/0.87  % (32609)------------------------------
% 4.25/0.93  % (32636)Time limit reached!
% 4.25/0.93  % (32636)------------------------------
% 4.25/0.93  % (32636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/0.94  % (32636)Termination reason: Time limit
% 4.48/0.94  
% 4.48/0.94  % (32636)Memory used [KB]: 3198
% 4.48/0.94  % (32636)Time elapsed: 0.521 s
% 4.48/0.94  % (32636)------------------------------
% 4.48/0.94  % (32636)------------------------------
% 4.48/0.97  % (32621)Time limit reached!
% 4.48/0.97  % (32621)------------------------------
% 4.48/0.97  % (32621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/0.97  % (32613)Time limit reached!
% 4.48/0.97  % (32613)------------------------------
% 4.48/0.97  % (32613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/0.97  % (32613)Termination reason: Time limit
% 4.48/0.97  
% 4.48/0.97  % (32613)Memory used [KB]: 14711
% 4.48/0.97  % (32613)Time elapsed: 0.522 s
% 4.48/0.97  % (32613)------------------------------
% 4.48/0.97  % (32613)------------------------------
% 4.48/0.98  % (32621)Termination reason: Time limit
% 4.48/0.98  
% 4.48/0.98  % (32621)Memory used [KB]: 5500
% 4.48/0.98  % (32621)Time elapsed: 0.524 s
% 4.48/0.98  % (32621)------------------------------
% 4.48/0.98  % (32621)------------------------------
% 4.48/0.98  % (355)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.48/1.02  % (360)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.48/1.02  % (32614)Time limit reached!
% 4.48/1.02  % (32614)------------------------------
% 4.48/1.02  % (32614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/1.02  % (32614)Termination reason: Time limit
% 4.48/1.02  
% 4.48/1.02  % (32614)Memory used [KB]: 5500
% 4.48/1.02  % (32614)Time elapsed: 0.609 s
% 4.48/1.02  % (32614)------------------------------
% 4.48/1.02  % (32614)------------------------------
% 5.13/1.07  % (399)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 5.52/1.09  % (401)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.52/1.10  % (400)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.52/1.11  % (360)Refutation found. Thanks to Tanya!
% 5.52/1.11  % SZS status Theorem for theBenchmark
% 5.52/1.11  % SZS output start Proof for theBenchmark
% 5.52/1.11  fof(f1490,plain,(
% 5.52/1.11    $false),
% 5.52/1.11    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f114,f119,f176,f182,f788,f808,f838,f968,f983,f1004,f1038,f1077,f1151,f1483])).
% 5.52/1.11  fof(f1483,plain,(
% 5.52/1.11    ~spl3_2 | ~spl3_3 | spl3_53),
% 5.52/1.11    inference(avatar_contradiction_clause,[],[f1482])).
% 5.52/1.11  fof(f1482,plain,(
% 5.52/1.11    $false | (~spl3_2 | ~spl3_3 | spl3_53)),
% 5.52/1.11    inference(subsumption_resolution,[],[f1481,f100])).
% 5.52/1.11  fof(f100,plain,(
% 5.52/1.11    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 5.52/1.11    inference(avatar_component_clause,[],[f98])).
% 5.52/1.11  fof(f98,plain,(
% 5.52/1.11    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.52/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 5.52/1.11  fof(f1481,plain,(
% 5.52/1.11    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_53)),
% 5.52/1.11    inference(subsumption_resolution,[],[f1475,f95])).
% 5.52/1.11  fof(f95,plain,(
% 5.52/1.11    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 5.52/1.11    inference(avatar_component_clause,[],[f93])).
% 5.52/1.11  fof(f93,plain,(
% 5.52/1.11    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.52/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 5.52/1.11  fof(f1475,plain,(
% 5.52/1.11    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_53),
% 5.52/1.11    inference(resolution,[],[f978,f77])).
% 5.52/1.11  fof(f77,plain,(
% 5.52/1.11    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.52/1.11    inference(cnf_transformation,[],[f40])).
% 5.52/1.11  fof(f40,plain,(
% 5.52/1.11    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.52/1.11    inference(flattening,[],[f39])).
% 5.52/1.11  fof(f39,plain,(
% 5.52/1.11    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.52/1.11    inference(ennf_transformation,[],[f12])).
% 5.52/1.11  fof(f12,axiom,(
% 5.52/1.11    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 5.52/1.11  fof(f978,plain,(
% 5.52/1.11    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_53),
% 5.52/1.11    inference(avatar_component_clause,[],[f976])).
% 5.52/1.11  fof(f976,plain,(
% 5.52/1.11    spl3_53 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.52/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 5.52/1.11  fof(f1151,plain,(
% 5.52/1.11    ~spl3_2 | ~spl3_3 | spl3_58),
% 5.52/1.11    inference(avatar_contradiction_clause,[],[f1150])).
% 5.52/1.11  fof(f1150,plain,(
% 5.52/1.11    $false | (~spl3_2 | ~spl3_3 | spl3_58)),
% 5.52/1.11    inference(subsumption_resolution,[],[f1149,f100])).
% 5.52/1.11  fof(f1149,plain,(
% 5.52/1.11    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_58)),
% 5.52/1.11    inference(subsumption_resolution,[],[f1148,f95])).
% 5.52/1.11  fof(f1148,plain,(
% 5.52/1.11    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_58),
% 5.52/1.11    inference(subsumption_resolution,[],[f1141,f85])).
% 5.52/1.11  fof(f85,plain,(
% 5.52/1.11    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.52/1.11    inference(equality_resolution,[],[f68])).
% 5.52/1.11  fof(f68,plain,(
% 5.52/1.11    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 5.52/1.11    inference(cnf_transformation,[],[f49])).
% 5.52/1.11  fof(f49,plain,(
% 5.52/1.11    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.52/1.11    inference(flattening,[],[f48])).
% 5.52/1.11  fof(f48,plain,(
% 5.52/1.11    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.52/1.11    inference(nnf_transformation,[],[f1])).
% 5.52/1.11  fof(f1,axiom,(
% 5.52/1.11    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.52/1.11  fof(f1141,plain,(
% 5.52/1.11    ~r1_tarski(sK2,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_58),
% 5.52/1.11    inference(resolution,[],[f1037,f249])).
% 5.52/1.11  fof(f249,plain,(
% 5.52/1.11    ( ! [X10,X8,X11,X9] : (r1_tarski(X11,k4_subset_1(X10,X8,X9)) | ~r1_tarski(X11,X9) | ~m1_subset_1(X9,k1_zfmisc_1(X10)) | ~m1_subset_1(X8,k1_zfmisc_1(X10))) )),
% 5.52/1.11    inference(superposition,[],[f80,f83])).
% 5.52/1.11  fof(f83,plain,(
% 5.52/1.11    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.52/1.11    inference(definition_unfolding,[],[f78,f79])).
% 5.52/1.11  fof(f79,plain,(
% 5.52/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 5.52/1.11    inference(definition_unfolding,[],[f60,f61])).
% 5.52/1.11  fof(f61,plain,(
% 5.52/1.11    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 5.52/1.11    inference(cnf_transformation,[],[f7])).
% 5.52/1.11  fof(f7,axiom,(
% 5.52/1.11    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 5.52/1.11  fof(f60,plain,(
% 5.52/1.11    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 5.52/1.11    inference(cnf_transformation,[],[f8])).
% 5.52/1.11  fof(f8,axiom,(
% 5.52/1.11    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 5.52/1.11  fof(f78,plain,(
% 5.52/1.11    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.52/1.11    inference(cnf_transformation,[],[f42])).
% 5.52/1.11  fof(f42,plain,(
% 5.52/1.11    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.52/1.11    inference(flattening,[],[f41])).
% 5.52/1.11  fof(f41,plain,(
% 5.52/1.11    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.52/1.11    inference(ennf_transformation,[],[f14])).
% 5.52/1.11  fof(f14,axiom,(
% 5.52/1.11    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 5.52/1.11  fof(f80,plain,(
% 5.52/1.11    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 5.52/1.11    inference(definition_unfolding,[],[f72,f79])).
% 5.52/1.11  fof(f72,plain,(
% 5.52/1.11    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 5.52/1.11    inference(cnf_transformation,[],[f31])).
% 5.52/1.11  fof(f31,plain,(
% 5.52/1.11    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 5.52/1.11    inference(ennf_transformation,[],[f2])).
% 5.52/1.11  fof(f2,axiom,(
% 5.52/1.11    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 5.52/1.11  fof(f1037,plain,(
% 5.52/1.11    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_58),
% 5.52/1.11    inference(avatar_component_clause,[],[f1035])).
% 5.52/1.11  fof(f1035,plain,(
% 5.52/1.11    spl3_58 <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 5.52/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 5.52/1.11  fof(f1077,plain,(
% 5.52/1.11    ~spl3_2 | ~spl3_3 | spl3_54),
% 5.52/1.11    inference(avatar_contradiction_clause,[],[f1076])).
% 5.52/1.11  fof(f1076,plain,(
% 5.52/1.11    $false | (~spl3_2 | ~spl3_3 | spl3_54)),
% 5.52/1.11    inference(subsumption_resolution,[],[f1075,f55])).
% 5.52/1.11  fof(f55,plain,(
% 5.52/1.11    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 5.52/1.11    inference(cnf_transformation,[],[f4])).
% 5.52/1.11  fof(f4,axiom,(
% 5.52/1.11    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 5.52/1.11  fof(f1075,plain,(
% 5.52/1.11    ~r1_tarski(k1_xboole_0,sK2) | (~spl3_2 | ~spl3_3 | spl3_54)),
% 5.52/1.11    inference(forward_demodulation,[],[f1074,f544])).
% 5.52/1.11  fof(f544,plain,(
% 5.52/1.11    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 5.52/1.11    inference(subsumption_resolution,[],[f536,f57])).
% 5.52/1.11  fof(f57,plain,(
% 5.52/1.11    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 5.52/1.11    inference(cnf_transformation,[],[f16])).
% 5.52/1.11  fof(f16,axiom,(
% 5.52/1.11    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 5.52/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 5.52/1.11  fof(f536,plain,(
% 5.52/1.11    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7))) )),
% 5.52/1.11    inference(superposition,[],[f162,f512])).
% 5.52/1.11  fof(f512,plain,(
% 5.52/1.11    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 5.52/1.11    inference(subsumption_resolution,[],[f504,f57])).
% 5.52/1.11  fof(f504,plain,(
% 5.52/1.11    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 5.52/1.11    inference(resolution,[],[f222,f55])).
% 5.52/1.12  fof(f222,plain,(
% 5.52/1.12    ( ! [X2,X3] : (~r1_tarski(X3,k3_subset_1(X2,X3)) | k3_subset_1(X2,X3) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 5.52/1.12    inference(subsumption_resolution,[],[f219,f62])).
% 5.52/1.12  fof(f62,plain,(
% 5.52/1.12    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.52/1.12    inference(cnf_transformation,[],[f27])).
% 5.52/1.12  fof(f27,plain,(
% 5.52/1.12    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.52/1.12    inference(ennf_transformation,[],[f11])).
% 5.52/1.12  fof(f11,axiom,(
% 5.52/1.12    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 5.52/1.12  fof(f219,plain,(
% 5.52/1.12    ( ! [X2,X3] : (~r1_tarski(X3,k3_subset_1(X2,X3)) | k3_subset_1(X2,X3) = X2 | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 5.52/1.12    inference(superposition,[],[f213,f64])).
% 5.52/1.12  fof(f64,plain,(
% 5.52/1.12    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.52/1.12    inference(cnf_transformation,[],[f29])).
% 5.52/1.12  fof(f29,plain,(
% 5.52/1.12    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.52/1.12    inference(ennf_transformation,[],[f13])).
% 5.52/1.12  fof(f13,axiom,(
% 5.52/1.12    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 5.52/1.12  fof(f213,plain,(
% 5.52/1.12    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.52/1.12    inference(forward_demodulation,[],[f65,f56])).
% 5.52/1.12  fof(f56,plain,(
% 5.52/1.12    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 5.52/1.12    inference(cnf_transformation,[],[f9])).
% 5.52/1.12  fof(f9,axiom,(
% 5.52/1.12    ! [X0] : k2_subset_1(X0) = X0),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 5.52/1.12  fof(f65,plain,(
% 5.52/1.12    ( ! [X0,X1] : (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.52/1.12    inference(cnf_transformation,[],[f47])).
% 5.52/1.12  fof(f47,plain,(
% 5.52/1.12    ! [X0,X1] : (((r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1) & (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.52/1.12    inference(nnf_transformation,[],[f30])).
% 5.52/1.12  fof(f30,plain,(
% 5.52/1.12    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.52/1.12    inference(ennf_transformation,[],[f15])).
% 5.52/1.12  fof(f15,axiom,(
% 5.52/1.12    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 5.52/1.12  fof(f162,plain,(
% 5.52/1.12    ( ! [X2,X3] : (k4_xboole_0(X2,k3_subset_1(X2,X3)) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 5.52/1.12    inference(subsumption_resolution,[],[f158,f62])).
% 5.52/1.12  fof(f158,plain,(
% 5.52/1.12    ( ! [X2,X3] : (k4_xboole_0(X2,k3_subset_1(X2,X3)) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 5.52/1.12    inference(superposition,[],[f64,f63])).
% 5.52/1.12  fof(f63,plain,(
% 5.52/1.12    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.52/1.12    inference(cnf_transformation,[],[f28])).
% 5.52/1.12  fof(f28,plain,(
% 5.52/1.12    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.52/1.12    inference(ennf_transformation,[],[f10])).
% 5.52/1.12  fof(f10,axiom,(
% 5.52/1.12    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 5.52/1.12  fof(f1074,plain,(
% 5.52/1.12    ~r1_tarski(k4_xboole_0(sK1,sK1),sK2) | (~spl3_2 | ~spl3_3 | spl3_54)),
% 5.52/1.12    inference(subsumption_resolution,[],[f1073,f100])).
% 5.52/1.12  fof(f1073,plain,(
% 5.52/1.12    ~r1_tarski(k4_xboole_0(sK1,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_54)),
% 5.52/1.12    inference(subsumption_resolution,[],[f1068,f95])).
% 5.52/1.12  fof(f1068,plain,(
% 5.52/1.12    ~r1_tarski(k4_xboole_0(sK1,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_54),
% 5.52/1.12    inference(resolution,[],[f982,f248])).
% 5.52/1.12  fof(f248,plain,(
% 5.52/1.12    ( ! [X6,X4,X7,X5] : (r1_tarski(X7,k4_subset_1(X6,X4,X5)) | ~r1_tarski(k4_xboole_0(X7,X4),X5) | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~m1_subset_1(X4,k1_zfmisc_1(X6))) )),
% 5.52/1.12    inference(superposition,[],[f81,f83])).
% 5.52/1.12  fof(f81,plain,(
% 5.52/1.12    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 5.52/1.12    inference(definition_unfolding,[],[f73,f79])).
% 5.52/1.12  fof(f73,plain,(
% 5.52/1.12    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f32])).
% 5.52/1.12  fof(f32,plain,(
% 5.52/1.12    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 5.52/1.12    inference(ennf_transformation,[],[f5])).
% 5.52/1.12  fof(f5,axiom,(
% 5.52/1.12    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 5.52/1.12  fof(f982,plain,(
% 5.52/1.12    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_54),
% 5.52/1.12    inference(avatar_component_clause,[],[f980])).
% 5.52/1.12  fof(f980,plain,(
% 5.52/1.12    spl3_54 <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 5.52/1.12  fof(f1038,plain,(
% 5.52/1.12    ~spl3_53 | ~spl3_58 | ~spl3_2 | ~spl3_4 | spl3_43),
% 5.52/1.12    inference(avatar_split_clause,[],[f1033,f785,f103,f93,f1035,f976])).
% 5.52/1.12  fof(f103,plain,(
% 5.52/1.12    spl3_4 <=> l1_pre_topc(sK0)),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 5.52/1.12  fof(f785,plain,(
% 5.52/1.12    spl3_43 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 5.52/1.12  fof(f1033,plain,(
% 5.52/1.12    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_4 | spl3_43)),
% 5.52/1.12    inference(subsumption_resolution,[],[f1032,f105])).
% 5.52/1.12  fof(f105,plain,(
% 5.52/1.12    l1_pre_topc(sK0) | ~spl3_4),
% 5.52/1.12    inference(avatar_component_clause,[],[f103])).
% 5.52/1.12  fof(f1032,plain,(
% 5.52/1.12    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_2 | spl3_43)),
% 5.52/1.12    inference(subsumption_resolution,[],[f1028,f95])).
% 5.52/1.12  fof(f1028,plain,(
% 5.52/1.12    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_43),
% 5.52/1.12    inference(resolution,[],[f787,f59])).
% 5.52/1.12  fof(f59,plain,(
% 5.52/1.12    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f26])).
% 5.52/1.12  fof(f26,plain,(
% 5.52/1.12    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.52/1.12    inference(flattening,[],[f25])).
% 5.52/1.12  fof(f25,plain,(
% 5.52/1.12    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.52/1.12    inference(ennf_transformation,[],[f20])).
% 5.52/1.12  fof(f20,axiom,(
% 5.52/1.12    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 5.52/1.12  fof(f787,plain,(
% 5.52/1.12    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_43),
% 5.52/1.12    inference(avatar_component_clause,[],[f785])).
% 5.52/1.12  fof(f1004,plain,(
% 5.52/1.12    ~spl3_5 | ~spl3_11 | spl3_52),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f1003])).
% 5.52/1.12  fof(f1003,plain,(
% 5.52/1.12    $false | (~spl3_5 | ~spl3_11 | spl3_52)),
% 5.52/1.12    inference(subsumption_resolution,[],[f998,f175])).
% 5.52/1.12  fof(f175,plain,(
% 5.52/1.12    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl3_11),
% 5.52/1.12    inference(avatar_component_clause,[],[f173])).
% 5.52/1.12  fof(f173,plain,(
% 5.52/1.12    spl3_11 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 5.52/1.12  fof(f998,plain,(
% 5.52/1.12    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl3_5 | spl3_52)),
% 5.52/1.12    inference(resolution,[],[f967,f145])).
% 5.52/1.12  fof(f145,plain,(
% 5.52/1.12    ( ! [X4] : (r1_tarski(X4,u1_struct_0(sK0)) | ~r1_tarski(X4,sK2)) ) | ~spl3_5),
% 5.52/1.12    inference(resolution,[],[f75,f113])).
% 5.52/1.12  fof(f113,plain,(
% 5.52/1.12    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_5),
% 5.52/1.12    inference(avatar_component_clause,[],[f111])).
% 5.52/1.12  fof(f111,plain,(
% 5.52/1.12    spl3_5 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 5.52/1.12  fof(f75,plain,(
% 5.52/1.12    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f36])).
% 5.52/1.12  fof(f36,plain,(
% 5.52/1.12    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 5.52/1.12    inference(flattening,[],[f35])).
% 5.52/1.12  fof(f35,plain,(
% 5.52/1.12    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 5.52/1.12    inference(ennf_transformation,[],[f3])).
% 5.52/1.12  fof(f3,axiom,(
% 5.52/1.12    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 5.52/1.12  fof(f967,plain,(
% 5.52/1.12    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_52),
% 5.52/1.12    inference(avatar_component_clause,[],[f965])).
% 5.52/1.12  fof(f965,plain,(
% 5.52/1.12    spl3_52 <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 5.52/1.12  fof(f983,plain,(
% 5.52/1.12    ~spl3_53 | ~spl3_54 | ~spl3_3 | ~spl3_4 | spl3_42),
% 5.52/1.12    inference(avatar_split_clause,[],[f974,f781,f103,f98,f980,f976])).
% 5.52/1.12  fof(f781,plain,(
% 5.52/1.12    spl3_42 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 5.52/1.12  fof(f974,plain,(
% 5.52/1.12    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_4 | spl3_42)),
% 5.52/1.12    inference(subsumption_resolution,[],[f973,f105])).
% 5.52/1.12  fof(f973,plain,(
% 5.52/1.12    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_3 | spl3_42)),
% 5.52/1.12    inference(subsumption_resolution,[],[f969,f100])).
% 5.52/1.12  fof(f969,plain,(
% 5.52/1.12    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_42),
% 5.52/1.12    inference(resolution,[],[f783,f59])).
% 5.52/1.12  fof(f783,plain,(
% 5.52/1.12    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_42),
% 5.52/1.12    inference(avatar_component_clause,[],[f781])).
% 5.52/1.12  fof(f968,plain,(
% 5.52/1.12    ~spl3_52 | spl3_41),
% 5.52/1.12    inference(avatar_split_clause,[],[f963,f777,f965])).
% 5.52/1.12  fof(f777,plain,(
% 5.52/1.12    spl3_41 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 5.52/1.12  fof(f963,plain,(
% 5.52/1.12    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_41),
% 5.52/1.12    inference(resolution,[],[f779,f71])).
% 5.52/1.12  fof(f71,plain,(
% 5.52/1.12    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f50])).
% 5.52/1.12  fof(f50,plain,(
% 5.52/1.12    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 5.52/1.12    inference(nnf_transformation,[],[f17])).
% 5.52/1.12  fof(f17,axiom,(
% 5.52/1.12    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 5.52/1.12  fof(f779,plain,(
% 5.52/1.12    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_41),
% 5.52/1.12    inference(avatar_component_clause,[],[f777])).
% 5.52/1.12  fof(f838,plain,(
% 5.52/1.12    ~spl3_6 | ~spl3_12 | spl3_46),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f837])).
% 5.52/1.12  fof(f837,plain,(
% 5.52/1.12    $false | (~spl3_6 | ~spl3_12 | spl3_46)),
% 5.52/1.12    inference(subsumption_resolution,[],[f831,f181])).
% 5.52/1.12  fof(f181,plain,(
% 5.52/1.12    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_12),
% 5.52/1.12    inference(avatar_component_clause,[],[f179])).
% 5.52/1.12  fof(f179,plain,(
% 5.52/1.12    spl3_12 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 5.52/1.12  fof(f831,plain,(
% 5.52/1.12    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_6 | spl3_46)),
% 5.52/1.12    inference(resolution,[],[f807,f146])).
% 5.52/1.12  fof(f146,plain,(
% 5.52/1.12    ( ! [X5] : (r1_tarski(X5,u1_struct_0(sK0)) | ~r1_tarski(X5,sK1)) ) | ~spl3_6),
% 5.52/1.12    inference(resolution,[],[f75,f118])).
% 5.52/1.12  fof(f118,plain,(
% 5.52/1.12    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 5.52/1.12    inference(avatar_component_clause,[],[f116])).
% 5.52/1.12  fof(f116,plain,(
% 5.52/1.12    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 5.52/1.12  fof(f807,plain,(
% 5.52/1.12    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_46),
% 5.52/1.12    inference(avatar_component_clause,[],[f805])).
% 5.52/1.12  fof(f805,plain,(
% 5.52/1.12    spl3_46 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 5.52/1.12  fof(f808,plain,(
% 5.52/1.12    ~spl3_46 | spl3_40),
% 5.52/1.12    inference(avatar_split_clause,[],[f803,f773,f805])).
% 5.52/1.12  fof(f773,plain,(
% 5.52/1.12    spl3_40 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 5.52/1.12  fof(f803,plain,(
% 5.52/1.12    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_40),
% 5.52/1.12    inference(resolution,[],[f775,f71])).
% 5.52/1.12  fof(f775,plain,(
% 5.52/1.12    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_40),
% 5.52/1.12    inference(avatar_component_clause,[],[f773])).
% 5.52/1.12  fof(f788,plain,(
% 5.52/1.12    ~spl3_40 | ~spl3_41 | ~spl3_42 | ~spl3_43 | spl3_1),
% 5.52/1.12    inference(avatar_split_clause,[],[f757,f88,f785,f781,f777,f773])).
% 5.52/1.12  fof(f88,plain,(
% 5.52/1.12    spl3_1 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 5.52/1.12  fof(f757,plain,(
% 5.52/1.12    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 5.52/1.12    inference(resolution,[],[f247,f90])).
% 5.52/1.12  fof(f90,plain,(
% 5.52/1.12    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_1),
% 5.52/1.12    inference(avatar_component_clause,[],[f88])).
% 5.52/1.12  fof(f247,plain,(
% 5.52/1.12    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_subset_1(X2,X0,X1),X3) | ~r1_tarski(X1,X3) | ~r1_tarski(X0,X3) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 5.52/1.12    inference(superposition,[],[f82,f83])).
% 5.52/1.12  fof(f82,plain,(
% 5.52/1.12    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 5.52/1.12    inference(definition_unfolding,[],[f76,f79])).
% 5.52/1.12  fof(f76,plain,(
% 5.52/1.12    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f38])).
% 5.52/1.12  fof(f38,plain,(
% 5.52/1.12    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 5.52/1.12    inference(flattening,[],[f37])).
% 5.52/1.12  fof(f37,plain,(
% 5.52/1.12    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 5.52/1.12    inference(ennf_transformation,[],[f6])).
% 5.52/1.12  fof(f6,axiom,(
% 5.52/1.12    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 5.52/1.12  fof(f182,plain,(
% 5.52/1.12    spl3_12 | ~spl3_3 | ~spl3_4),
% 5.52/1.12    inference(avatar_split_clause,[],[f177,f103,f98,f179])).
% 5.52/1.12  fof(f177,plain,(
% 5.52/1.12    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 5.52/1.12    inference(subsumption_resolution,[],[f167,f105])).
% 5.52/1.12  fof(f167,plain,(
% 5.52/1.12    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 5.52/1.12    inference(resolution,[],[f58,f100])).
% 5.52/1.12  fof(f58,plain,(
% 5.52/1.12    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f24])).
% 5.52/1.12  fof(f24,plain,(
% 5.52/1.12    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.52/1.12    inference(ennf_transformation,[],[f19])).
% 5.52/1.12  fof(f19,axiom,(
% 5.52/1.12    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 5.52/1.12  fof(f176,plain,(
% 5.52/1.12    spl3_11 | ~spl3_2 | ~spl3_4),
% 5.52/1.12    inference(avatar_split_clause,[],[f171,f103,f93,f173])).
% 5.52/1.12  fof(f171,plain,(
% 5.52/1.12    r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl3_2 | ~spl3_4)),
% 5.52/1.12    inference(subsumption_resolution,[],[f166,f105])).
% 5.52/1.12  fof(f166,plain,(
% 5.52/1.12    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0) | ~spl3_2),
% 5.52/1.12    inference(resolution,[],[f58,f95])).
% 5.52/1.12  fof(f119,plain,(
% 5.52/1.12    spl3_6 | ~spl3_3),
% 5.52/1.12    inference(avatar_split_clause,[],[f108,f98,f116])).
% 5.52/1.12  fof(f108,plain,(
% 5.52/1.12    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 5.52/1.12    inference(resolution,[],[f70,f100])).
% 5.52/1.12  fof(f70,plain,(
% 5.52/1.12    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f50])).
% 5.52/1.12  fof(f114,plain,(
% 5.52/1.12    spl3_5 | ~spl3_2),
% 5.52/1.12    inference(avatar_split_clause,[],[f107,f93,f111])).
% 5.52/1.12  fof(f107,plain,(
% 5.52/1.12    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_2),
% 5.52/1.12    inference(resolution,[],[f70,f95])).
% 5.52/1.12  fof(f106,plain,(
% 5.52/1.12    spl3_4),
% 5.52/1.12    inference(avatar_split_clause,[],[f51,f103])).
% 5.52/1.12  fof(f51,plain,(
% 5.52/1.12    l1_pre_topc(sK0)),
% 5.52/1.12    inference(cnf_transformation,[],[f46])).
% 5.52/1.12  fof(f46,plain,(
% 5.52/1.12    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 5.52/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f45,f44,f43])).
% 5.52/1.12  fof(f43,plain,(
% 5.52/1.12    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 5.52/1.12    introduced(choice_axiom,[])).
% 5.52/1.12  fof(f44,plain,(
% 5.52/1.12    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.52/1.12    introduced(choice_axiom,[])).
% 5.52/1.12  fof(f45,plain,(
% 5.52/1.12    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.52/1.12    introduced(choice_axiom,[])).
% 5.52/1.12  fof(f23,plain,(
% 5.52/1.12    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 5.52/1.12    inference(ennf_transformation,[],[f22])).
% 5.52/1.12  fof(f22,negated_conjecture,(
% 5.52/1.12    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 5.52/1.12    inference(negated_conjecture,[],[f21])).
% 5.52/1.12  fof(f21,conjecture,(
% 5.52/1.12    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 5.52/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).
% 5.52/1.12  fof(f101,plain,(
% 5.52/1.12    spl3_3),
% 5.52/1.12    inference(avatar_split_clause,[],[f52,f98])).
% 5.52/1.12  fof(f52,plain,(
% 5.52/1.12    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.52/1.12    inference(cnf_transformation,[],[f46])).
% 5.52/1.12  fof(f96,plain,(
% 5.52/1.12    spl3_2),
% 5.52/1.12    inference(avatar_split_clause,[],[f53,f93])).
% 5.52/1.12  fof(f53,plain,(
% 5.52/1.12    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.52/1.12    inference(cnf_transformation,[],[f46])).
% 5.52/1.12  fof(f91,plain,(
% 5.52/1.12    ~spl3_1),
% 5.52/1.12    inference(avatar_split_clause,[],[f54,f88])).
% 5.52/1.12  fof(f54,plain,(
% 5.52/1.12    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 5.52/1.12    inference(cnf_transformation,[],[f46])).
% 5.52/1.12  % SZS output end Proof for theBenchmark
% 5.52/1.12  % (360)------------------------------
% 5.52/1.12  % (360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.52/1.12  % (360)Termination reason: Refutation
% 5.52/1.12  
% 5.52/1.12  % (360)Memory used [KB]: 12025
% 5.52/1.12  % (360)Time elapsed: 0.200 s
% 5.52/1.12  % (360)------------------------------
% 5.52/1.12  % (360)------------------------------
% 5.52/1.12  % (32606)Success in time 0.76 s
%------------------------------------------------------------------------------
