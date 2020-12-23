%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 235 expanded)
%              Number of leaves         :   24 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  267 ( 491 expanded)
%              Number of equality atoms :  131 ( 274 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f713,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f58,f405,f492,f507,f514,f532,f571,f587,f591,f595,f701,f712])).

fof(f712,plain,
    ( spl4_3
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f711,f698,f51])).

fof(f51,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f698,plain,
    ( spl4_35
  <=> sK1 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f711,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl4_35 ),
    inference(trivial_inequality_removal,[],[f710])).

fof(f710,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f708,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f22,f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f708,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | r1_tarski(sK1,sK3)
    | ~ spl4_35 ),
    inference(superposition,[],[f38,f700])).

fof(f700,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f698])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f701,plain,
    ( spl4_35
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f696,f273,f698])).

fof(f273,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK1,sK3) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f696,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl4_14 ),
    inference(equality_resolution,[],[f274])).

fof(f274,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK1,sK3) = X1 )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f273])).

fof(f595,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | spl4_21 ),
    inference(trivial_inequality_removal,[],[f593])).

fof(f593,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_21 ),
    inference(superposition,[],[f418,f125])).

fof(f125,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f117,f37])).

fof(f117,plain,(
    ! [X5,X3] : k1_xboole_0 = k2_zfmisc_1(X3,k3_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,X5)))) ),
    inference(superposition,[],[f83,f93])).

fof(f93,plain,(
    ! [X12,X10,X11] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X10,k1_xboole_0),k2_zfmisc_1(X11,k3_tarski(k2_tarski(k1_xboole_0,X12)))) ),
    inference(resolution,[],[f69,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f69,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2)))) ),
    inference(resolution,[],[f35,f66])).

fof(f66,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,X0))) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) ) ),
    inference(superposition,[],[f27,f37])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X3)) = k2_zfmisc_1(X0,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f31,f37])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f418,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl4_21
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f591,plain,
    ( ~ spl4_21
    | spl4_1
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f406,f380,f41,f416])).

fof(f41,plain,
    ( spl4_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f380,plain,
    ( spl4_19
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f406,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl4_1
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f43,f382])).

fof(f382,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f380])).

fof(f43,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f587,plain,
    ( spl4_9
    | spl4_14
    | spl4_20
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f586,f376,f61,f384,f273,f231])).

fof(f231,plain,
    ( spl4_9
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f384,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f61,plain,
    ( spl4_5
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f376,plain,
    ( spl4_18
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f586,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = sK0
        | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | k3_xboole_0(sK1,sK3) = X1 )
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f535,f378])).

fof(f378,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f376])).

fof(f535,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = k3_xboole_0(sK0,sK2)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | k3_xboole_0(sK1,sK3) = X1 )
    | ~ spl4_5 ),
    inference(superposition,[],[f98,f63])).

fof(f63,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k3_xboole_0(X0,X1) = k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(X2,X3)
      | k3_xboole_0(X2,X3) = X5 ) ),
    inference(superposition,[],[f33,f31])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f571,plain,
    ( spl4_20
    | spl4_19
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f570,f231,f61,f380,f384])).

fof(f570,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(equality_resolution,[],[f546])).

fof(f546,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5)
        | k1_xboole_0 = X5
        | k1_xboole_0 = X4 )
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f545])).

fof(f545,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 = X5
        | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5)
        | k1_xboole_0 = X4
        | k1_xboole_0 = X5 )
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f537,f233])).

fof(f233,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f231])).

fof(f537,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5)
        | k1_xboole_0 = X4
        | k1_xboole_0 = X5
        | k3_xboole_0(sK1,sK3) = X5 )
    | ~ spl4_5 ),
    inference(superposition,[],[f99,f63])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | k3_xboole_0(X2,X3) = X5 ) ),
    inference(superposition,[],[f33,f31])).

fof(f532,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f530,f46,f61])).

fof(f46,plain,
    ( spl4_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f530,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f514,plain,(
    spl4_28 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | spl4_28 ),
    inference(trivial_inequality_removal,[],[f512])).

fof(f512,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_28 ),
    inference(superposition,[],[f470,f157])).

fof(f157,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f147,f37])).

fof(f147,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,X1))),X0) ),
    inference(superposition,[],[f84,f87])).

fof(f87,plain,(
    ! [X12,X10,X11] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k3_tarski(k2_tarski(k1_xboole_0,X11)),X12)) ),
    inference(resolution,[],[f67,f28])).

fof(f67,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k2_zfmisc_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2)) ),
    inference(resolution,[],[f66,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k3_tarski(k2_tarski(X0,X1)))) = k2_zfmisc_1(k3_xboole_0(X2,X3),X0) ),
    inference(superposition,[],[f31,f37])).

fof(f470,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl4_28
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f507,plain,
    ( spl4_4
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f398,f376,f55])).

fof(f55,plain,
    ( spl4_4
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f398,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_18 ),
    inference(trivial_inequality_removal,[],[f397])).

fof(f397,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f394,f70])).

fof(f394,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f38,f378])).

fof(f492,plain,
    ( ~ spl4_28
    | spl4_1
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f490,f384,f41,f468])).

fof(f490,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f43,f386])).

fof(f386,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f384])).

fof(f405,plain,
    ( spl4_18
    | spl4_19
    | spl4_20
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f404,f61,f384,f380,f376])).

fof(f404,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_5 ),
    inference(equality_resolution,[],[f181])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k3_xboole_0(sK0,sK2) = X0 )
    | ~ spl4_5 ),
    inference(superposition,[],[f89,f63])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | k3_xboole_0(X0,X1) = X4 ) ),
    inference(superposition,[],[f32,f31])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f19,f55,f51])).

fof(f19,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f49,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (31853)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (31859)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (31863)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (31869)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (31863)Refutation not found, incomplete strategy% (31863)------------------------------
% 0.20/0.51  % (31863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31863)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31863)Memory used [KB]: 10618
% 0.20/0.51  % (31863)Time elapsed: 0.063 s
% 0.20/0.51  % (31863)------------------------------
% 0.20/0.51  % (31863)------------------------------
% 0.20/0.52  % (31847)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (31867)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (31864)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (31842)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (31870)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (31851)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (31854)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (31846)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (31843)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (31849)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (31841)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (31852)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (31868)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (31860)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (31844)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (31855)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (31856)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (31845)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (31861)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (31865)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (31848)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (31866)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (31858)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (31858)Refutation not found, incomplete strategy% (31858)------------------------------
% 0.20/0.55  % (31858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31858)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31858)Memory used [KB]: 10618
% 0.20/0.55  % (31858)Time elapsed: 0.143 s
% 0.20/0.55  % (31858)------------------------------
% 0.20/0.55  % (31858)------------------------------
% 0.20/0.55  % (31850)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (31857)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (31856)Refutation not found, incomplete strategy% (31856)------------------------------
% 0.20/0.56  % (31856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (31856)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (31856)Memory used [KB]: 6268
% 0.20/0.57  % (31856)Time elapsed: 0.137 s
% 0.20/0.57  % (31856)------------------------------
% 0.20/0.57  % (31856)------------------------------
% 0.20/0.57  % (31862)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.60  % (31857)Refutation found. Thanks to Tanya!
% 0.20/0.60  % SZS status Theorem for theBenchmark
% 0.20/0.60  % SZS output start Proof for theBenchmark
% 0.20/0.60  fof(f713,plain,(
% 0.20/0.60    $false),
% 0.20/0.60    inference(avatar_sat_refutation,[],[f44,f49,f58,f405,f492,f507,f514,f532,f571,f587,f591,f595,f701,f712])).
% 0.20/0.60  fof(f712,plain,(
% 0.20/0.60    spl4_3 | ~spl4_35),
% 0.20/0.60    inference(avatar_split_clause,[],[f711,f698,f51])).
% 0.20/0.60  fof(f51,plain,(
% 0.20/0.60    spl4_3 <=> r1_tarski(sK1,sK3)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.60  fof(f698,plain,(
% 0.20/0.60    spl4_35 <=> sK1 = k3_xboole_0(sK1,sK3)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.60  fof(f711,plain,(
% 0.20/0.60    r1_tarski(sK1,sK3) | ~spl4_35),
% 0.20/0.60    inference(trivial_inequality_removal,[],[f710])).
% 0.20/0.60  fof(f710,plain,(
% 0.20/0.60    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | ~spl4_35),
% 0.20/0.60    inference(forward_demodulation,[],[f708,f70])).
% 0.20/0.60  fof(f70,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.60    inference(forward_demodulation,[],[f36,f37])).
% 0.20/0.60  fof(f37,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0) )),
% 0.20/0.60    inference(definition_unfolding,[],[f23,f24])).
% 0.20/0.60  fof(f24,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f7])).
% 0.20/0.60  fof(f7,axiom,(
% 0.20/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.60  fof(f23,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.60    inference(cnf_transformation,[],[f4])).
% 0.20/0.60  fof(f4,axiom,(
% 0.20/0.60    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.60  fof(f36,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 0.20/0.60    inference(definition_unfolding,[],[f22,f25,f24])).
% 0.20/0.60  fof(f25,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f3])).
% 0.20/0.60  fof(f3,axiom,(
% 0.20/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.60  fof(f22,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f6])).
% 0.20/0.60  fof(f6,axiom,(
% 0.20/0.60    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.60  fof(f708,plain,(
% 0.20/0.60    k1_xboole_0 != k5_xboole_0(sK1,sK1) | r1_tarski(sK1,sK3) | ~spl4_35),
% 0.20/0.60    inference(superposition,[],[f38,f700])).
% 0.20/0.60  fof(f700,plain,(
% 0.20/0.60    sK1 = k3_xboole_0(sK1,sK3) | ~spl4_35),
% 0.20/0.60    inference(avatar_component_clause,[],[f698])).
% 0.20/0.60  fof(f38,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f30,f25])).
% 0.20/0.60  fof(f30,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f2])).
% 0.20/0.60  fof(f2,axiom,(
% 0.20/0.60    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.60  fof(f701,plain,(
% 0.20/0.60    spl4_35 | ~spl4_14),
% 0.20/0.60    inference(avatar_split_clause,[],[f696,f273,f698])).
% 0.20/0.60  fof(f273,plain,(
% 0.20/0.60    spl4_14 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK1,sK3) = X1)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.60  fof(f696,plain,(
% 0.20/0.60    sK1 = k3_xboole_0(sK1,sK3) | ~spl4_14),
% 0.20/0.60    inference(equality_resolution,[],[f274])).
% 0.20/0.60  fof(f274,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK1,sK3) = X1) ) | ~spl4_14),
% 0.20/0.60    inference(avatar_component_clause,[],[f273])).
% 0.20/0.60  fof(f595,plain,(
% 0.20/0.60    spl4_21),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f594])).
% 0.20/0.60  fof(f594,plain,(
% 0.20/0.60    $false | spl4_21),
% 0.20/0.60    inference(trivial_inequality_removal,[],[f593])).
% 0.20/0.60  fof(f593,plain,(
% 0.20/0.60    k1_xboole_0 != k1_xboole_0 | spl4_21),
% 0.20/0.60    inference(superposition,[],[f418,f125])).
% 0.20/0.60  fof(f125,plain,(
% 0.20/0.60    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0)) )),
% 0.20/0.60    inference(forward_demodulation,[],[f117,f37])).
% 0.20/0.60  fof(f117,plain,(
% 0.20/0.60    ( ! [X5,X3] : (k1_xboole_0 = k2_zfmisc_1(X3,k3_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,X5))))) )),
% 0.20/0.60    inference(superposition,[],[f83,f93])).
% 0.20/0.60  fof(f93,plain,(
% 0.20/0.60    ( ! [X12,X10,X11] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X10,k1_xboole_0),k2_zfmisc_1(X11,k3_tarski(k2_tarski(k1_xboole_0,X12))))) )),
% 0.20/0.60    inference(resolution,[],[f69,f28])).
% 0.20/0.60  fof(f28,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.60    inference(cnf_transformation,[],[f1])).
% 0.20/0.60  fof(f1,axiom,(
% 0.20/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.60  fof(f69,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X1,k3_tarski(k2_tarski(k1_xboole_0,X2))))) )),
% 0.20/0.60    inference(resolution,[],[f35,f66])).
% 0.20/0.60  fof(f66,plain,(
% 0.20/0.60    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,X0)))) )),
% 0.20/0.60    inference(equality_resolution,[],[f65])).
% 0.20/0.60  fof(f65,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.20/0.60    inference(superposition,[],[f27,f37])).
% 0.20/0.60  fof(f27,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f1])).
% 0.20/0.60  fof(f35,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f18])).
% 0.20/0.60  fof(f18,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.60    inference(ennf_transformation,[],[f9])).
% 0.20/0.60  fof(f9,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.20/0.60  fof(f83,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X3)) = k2_zfmisc_1(X0,k3_xboole_0(X2,X3))) )),
% 0.20/0.60    inference(superposition,[],[f31,f37])).
% 0.20/0.60  fof(f31,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f8])).
% 0.20/0.60  fof(f8,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.20/0.60  fof(f418,plain,(
% 0.20/0.60    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl4_21),
% 0.20/0.60    inference(avatar_component_clause,[],[f416])).
% 0.20/0.61  fof(f416,plain,(
% 0.20/0.61    spl4_21 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.61  fof(f591,plain,(
% 0.20/0.61    ~spl4_21 | spl4_1 | ~spl4_19),
% 0.20/0.61    inference(avatar_split_clause,[],[f406,f380,f41,f416])).
% 0.20/0.61  fof(f41,plain,(
% 0.20/0.61    spl4_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.61  fof(f380,plain,(
% 0.20/0.61    spl4_19 <=> k1_xboole_0 = sK1),
% 0.20/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.61  fof(f406,plain,(
% 0.20/0.61    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl4_1 | ~spl4_19)),
% 0.20/0.61    inference(backward_demodulation,[],[f43,f382])).
% 0.20/0.61  fof(f382,plain,(
% 0.20/0.61    k1_xboole_0 = sK1 | ~spl4_19),
% 0.20/0.61    inference(avatar_component_clause,[],[f380])).
% 0.20/0.61  fof(f43,plain,(
% 0.20/0.61    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl4_1),
% 0.20/0.61    inference(avatar_component_clause,[],[f41])).
% 0.20/0.61  fof(f587,plain,(
% 0.20/0.61    spl4_9 | spl4_14 | spl4_20 | ~spl4_5 | ~spl4_18),
% 0.20/0.61    inference(avatar_split_clause,[],[f586,f376,f61,f384,f273,f231])).
% 0.20/0.61  fof(f231,plain,(
% 0.20/0.61    spl4_9 <=> k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 0.20/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.61  fof(f384,plain,(
% 0.20/0.61    spl4_20 <=> k1_xboole_0 = sK0),
% 0.20/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.61  fof(f61,plain,(
% 0.20/0.61    spl4_5 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.61  fof(f376,plain,(
% 0.20/0.61    spl4_18 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 0.20/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.61  fof(f586,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k1_xboole_0 = sK0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k3_xboole_0(sK1,sK3) = X1) ) | (~spl4_5 | ~spl4_18)),
% 0.20/0.61    inference(forward_demodulation,[],[f535,f378])).
% 0.20/0.61  fof(f378,plain,(
% 0.20/0.61    sK0 = k3_xboole_0(sK0,sK2) | ~spl4_18),
% 0.20/0.61    inference(avatar_component_clause,[],[f376])).
% 1.93/0.61  fof(f535,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k3_xboole_0(sK1,sK3) = X1) ) | ~spl4_5),
% 1.93/0.61    inference(superposition,[],[f98,f63])).
% 1.93/0.61  fof(f63,plain,(
% 1.93/0.61    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_5),
% 1.93/0.61    inference(avatar_component_clause,[],[f61])).
% 1.93/0.61  fof(f98,plain,(
% 1.93/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k3_xboole_0(X0,X1) = k1_xboole_0 | k1_xboole_0 = k3_xboole_0(X2,X3) | k3_xboole_0(X2,X3) = X5) )),
% 1.93/0.61    inference(superposition,[],[f33,f31])).
% 1.93/0.61  fof(f33,plain,(
% 1.93/0.61    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X1 = X3) )),
% 1.93/0.61    inference(cnf_transformation,[],[f17])).
% 1.93/0.61  fof(f17,plain,(
% 1.93/0.61    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 1.93/0.61    inference(flattening,[],[f16])).
% 1.93/0.61  fof(f16,plain,(
% 1.93/0.61    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 1.93/0.61    inference(ennf_transformation,[],[f10])).
% 1.93/0.61  fof(f10,axiom,(
% 1.93/0.61    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.93/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.93/0.61  fof(f571,plain,(
% 1.93/0.61    spl4_20 | spl4_19 | ~spl4_5 | ~spl4_9),
% 1.93/0.61    inference(avatar_split_clause,[],[f570,f231,f61,f380,f384])).
% 1.93/0.61  fof(f570,plain,(
% 1.93/0.61    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl4_5 | ~spl4_9)),
% 1.93/0.61    inference(equality_resolution,[],[f546])).
% 1.93/0.61  fof(f546,plain,(
% 1.93/0.61    ( ! [X4,X5] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = X5 | k1_xboole_0 = X4) ) | (~spl4_5 | ~spl4_9)),
% 1.93/0.61    inference(duplicate_literal_removal,[],[f545])).
% 1.93/0.61  fof(f545,plain,(
% 1.93/0.61    ( ! [X4,X5] : (k1_xboole_0 = X5 | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = X4 | k1_xboole_0 = X5) ) | (~spl4_5 | ~spl4_9)),
% 1.93/0.61    inference(forward_demodulation,[],[f537,f233])).
% 1.93/0.61  fof(f233,plain,(
% 1.93/0.61    k1_xboole_0 = k3_xboole_0(sK1,sK3) | ~spl4_9),
% 1.93/0.61    inference(avatar_component_clause,[],[f231])).
% 1.93/0.61  fof(f537,plain,(
% 1.93/0.61    ( ! [X4,X5] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k3_xboole_0(sK1,sK3) = X5) ) | ~spl4_5),
% 1.93/0.61    inference(superposition,[],[f99,f63])).
% 1.93/0.61  fof(f99,plain,(
% 1.93/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k3_xboole_0(X2,X3) = X5) )),
% 1.93/0.61    inference(superposition,[],[f33,f31])).
% 1.93/0.61  fof(f532,plain,(
% 1.93/0.61    spl4_5 | ~spl4_2),
% 1.93/0.61    inference(avatar_split_clause,[],[f530,f46,f61])).
% 1.93/0.61  fof(f46,plain,(
% 1.93/0.61    spl4_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.93/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.93/0.61  fof(f530,plain,(
% 1.93/0.61    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_2),
% 1.93/0.61    inference(resolution,[],[f48,f26])).
% 1.93/0.61  fof(f26,plain,(
% 1.93/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.93/0.61    inference(cnf_transformation,[],[f15])).
% 1.93/0.61  fof(f15,plain,(
% 1.93/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.93/0.61    inference(ennf_transformation,[],[f5])).
% 1.93/0.61  fof(f5,axiom,(
% 1.93/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.93/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.93/0.61  fof(f48,plain,(
% 1.93/0.61    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_2),
% 1.93/0.61    inference(avatar_component_clause,[],[f46])).
% 1.93/0.61  fof(f514,plain,(
% 1.93/0.61    spl4_28),
% 1.93/0.61    inference(avatar_contradiction_clause,[],[f513])).
% 1.93/0.61  fof(f513,plain,(
% 1.93/0.61    $false | spl4_28),
% 1.93/0.61    inference(trivial_inequality_removal,[],[f512])).
% 1.93/0.61  fof(f512,plain,(
% 1.93/0.61    k1_xboole_0 != k1_xboole_0 | spl4_28),
% 1.93/0.61    inference(superposition,[],[f470,f157])).
% 1.93/0.61  fof(f157,plain,(
% 1.93/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.93/0.61    inference(forward_demodulation,[],[f147,f37])).
% 1.93/0.61  fof(f147,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,X1))),X0)) )),
% 1.93/0.61    inference(superposition,[],[f84,f87])).
% 1.93/0.61  fof(f87,plain,(
% 1.93/0.61    ( ! [X12,X10,X11] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X10),k2_zfmisc_1(k3_tarski(k2_tarski(k1_xboole_0,X11)),X12))) )),
% 1.93/0.61    inference(resolution,[],[f67,f28])).
% 1.93/0.61  fof(f67,plain,(
% 1.93/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k2_zfmisc_1(k3_tarski(k2_tarski(k1_xboole_0,X1)),X2))) )),
% 1.93/0.61    inference(resolution,[],[f66,f34])).
% 1.93/0.61  fof(f34,plain,(
% 1.93/0.61    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f18])).
% 1.93/0.61  fof(f84,plain,(
% 1.93/0.61    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k3_tarski(k2_tarski(X0,X1)))) = k2_zfmisc_1(k3_xboole_0(X2,X3),X0)) )),
% 1.93/0.61    inference(superposition,[],[f31,f37])).
% 1.93/0.61  fof(f470,plain,(
% 1.93/0.61    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl4_28),
% 1.93/0.61    inference(avatar_component_clause,[],[f468])).
% 1.93/0.61  fof(f468,plain,(
% 1.93/0.61    spl4_28 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.93/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.93/0.61  fof(f507,plain,(
% 1.93/0.61    spl4_4 | ~spl4_18),
% 1.93/0.61    inference(avatar_split_clause,[],[f398,f376,f55])).
% 1.93/0.61  fof(f55,plain,(
% 1.93/0.61    spl4_4 <=> r1_tarski(sK0,sK2)),
% 1.93/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.93/0.61  fof(f398,plain,(
% 1.93/0.61    r1_tarski(sK0,sK2) | ~spl4_18),
% 1.93/0.61    inference(trivial_inequality_removal,[],[f397])).
% 1.93/0.61  fof(f397,plain,(
% 1.93/0.61    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | ~spl4_18),
% 1.93/0.61    inference(forward_demodulation,[],[f394,f70])).
% 1.93/0.61  fof(f394,plain,(
% 1.93/0.61    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,sK2) | ~spl4_18),
% 1.93/0.61    inference(superposition,[],[f38,f378])).
% 1.93/0.61  fof(f492,plain,(
% 1.93/0.61    ~spl4_28 | spl4_1 | ~spl4_20),
% 1.93/0.61    inference(avatar_split_clause,[],[f490,f384,f41,f468])).
% 1.93/0.61  fof(f490,plain,(
% 1.93/0.61    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_20)),
% 1.93/0.61    inference(backward_demodulation,[],[f43,f386])).
% 1.93/0.61  fof(f386,plain,(
% 1.93/0.61    k1_xboole_0 = sK0 | ~spl4_20),
% 1.93/0.61    inference(avatar_component_clause,[],[f384])).
% 1.93/0.61  fof(f405,plain,(
% 1.93/0.61    spl4_18 | spl4_19 | spl4_20 | ~spl4_5),
% 1.93/0.61    inference(avatar_split_clause,[],[f404,f61,f384,f380,f376])).
% 1.93/0.61  fof(f404,plain,(
% 1.93/0.61    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | sK0 = k3_xboole_0(sK0,sK2) | ~spl4_5),
% 1.93/0.61    inference(equality_resolution,[],[f181])).
% 1.93/0.61  fof(f181,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k3_xboole_0(sK0,sK2) = X0) ) | ~spl4_5),
% 1.93/0.61    inference(superposition,[],[f89,f63])).
% 1.93/0.61  fof(f89,plain,(
% 1.93/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k3_xboole_0(X0,X1) = X4) )),
% 1.93/0.61    inference(superposition,[],[f32,f31])).
% 1.93/0.61  fof(f32,plain,(
% 1.93/0.61    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X0 = X2) )),
% 1.93/0.61    inference(cnf_transformation,[],[f17])).
% 1.93/0.61  fof(f58,plain,(
% 1.93/0.61    ~spl4_3 | ~spl4_4),
% 1.93/0.61    inference(avatar_split_clause,[],[f19,f55,f51])).
% 1.93/0.61  fof(f19,plain,(
% 1.93/0.61    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 1.93/0.61    inference(cnf_transformation,[],[f14])).
% 1.93/0.61  fof(f14,plain,(
% 1.93/0.61    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.93/0.61    inference(flattening,[],[f13])).
% 1.93/0.61  fof(f13,plain,(
% 1.93/0.61    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.93/0.61    inference(ennf_transformation,[],[f12])).
% 1.93/0.61  fof(f12,negated_conjecture,(
% 1.93/0.61    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.93/0.61    inference(negated_conjecture,[],[f11])).
% 1.93/0.61  fof(f11,conjecture,(
% 1.93/0.61    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.93/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.93/0.61  fof(f49,plain,(
% 1.93/0.61    spl4_2),
% 1.93/0.61    inference(avatar_split_clause,[],[f20,f46])).
% 1.93/0.61  fof(f20,plain,(
% 1.93/0.61    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.93/0.61    inference(cnf_transformation,[],[f14])).
% 1.93/0.61  fof(f44,plain,(
% 1.93/0.61    ~spl4_1),
% 1.93/0.61    inference(avatar_split_clause,[],[f21,f41])).
% 1.93/0.61  fof(f21,plain,(
% 1.93/0.61    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.93/0.61    inference(cnf_transformation,[],[f14])).
% 1.93/0.61  % SZS output end Proof for theBenchmark
% 1.93/0.61  % (31857)------------------------------
% 1.93/0.61  % (31857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.61  % (31857)Termination reason: Refutation
% 1.93/0.61  
% 1.93/0.61  % (31857)Memory used [KB]: 11129
% 1.93/0.61  % (31857)Time elapsed: 0.197 s
% 1.93/0.61  % (31857)------------------------------
% 1.93/0.61  % (31857)------------------------------
% 1.93/0.62  % (31840)Success in time 0.25 s
%------------------------------------------------------------------------------
