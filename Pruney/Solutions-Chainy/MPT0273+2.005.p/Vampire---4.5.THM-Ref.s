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
% DateTime   : Thu Dec  3 12:41:18 EST 2020

% Result     : Theorem 41.34s
% Output     : Refutation 41.34s
% Verified   : 
% Statistics : Number of formulae       :  174 (4362 expanded)
%              Number of leaves         :   25 (1469 expanded)
%              Depth                    :   35
%              Number of atoms          :  359 (5365 expanded)
%              Number of equality atoms :  161 (4198 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f121,f126,f127,f1182,f18818,f20417,f20426,f34624,f61280,f84925,f85105,f85157])).

fof(f85157,plain,
    ( ~ spl5_4
    | ~ spl5_131 ),
    inference(avatar_contradiction_clause,[],[f85134])).

fof(f85134,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_131 ),
    inference(unit_resulting_resolution,[],[f124,f84924,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f84924,plain,
    ( r2_hidden(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ spl5_131 ),
    inference(avatar_component_clause,[],[f84922])).

fof(f84922,plain,
    ( spl5_131
  <=> r2_hidden(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f124,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_4
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f85105,plain,
    ( spl5_2
    | spl5_130 ),
    inference(avatar_contradiction_clause,[],[f85090])).

fof(f85090,plain,
    ( $false
    | spl5_2
    | spl5_130 ),
    inference(unit_resulting_resolution,[],[f115,f104,f84920,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f84920,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl5_130 ),
    inference(avatar_component_clause,[],[f84918])).

fof(f84918,plain,
    ( spl5_130
  <=> r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f104,plain,(
    ! [X4,X2,X0] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X4,X2)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X3] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X4,X2) != X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f70,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f115,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f84925,plain,
    ( ~ spl5_130
    | spl5_131
    | spl5_1
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f84824,f34538,f109,f84922,f84918])).

fof(f109,plain,
    ( spl5_1
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f34538,plain,
    ( spl5_81
  <=> ! [X89,X90] : k4_xboole_0(X89,X90) = k4_xboole_0(X89,k4_xboole_0(X90,k4_xboole_0(X90,X89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f84824,plain,
    ( r2_hidden(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl5_1
    | ~ spl5_81 ),
    inference(trivial_inequality_removal,[],[f84507])).

fof(f84507,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | r2_hidden(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl5_1
    | ~ spl5_81 ),
    inference(superposition,[],[f110,f83587])).

fof(f83587,plain,
    ( ! [X19,X20,X18] :
        ( k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),X20) = k3_enumset1(X18,X18,X18,X18,X18)
        | r2_hidden(X19,k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),X20))
        | ~ r2_hidden(X18,k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),X20)) )
    | ~ spl5_81 ),
    inference(forward_demodulation,[],[f1894,f34539])).

fof(f34539,plain,
    ( ! [X90,X89] : k4_xboole_0(X89,X90) = k4_xboole_0(X89,k4_xboole_0(X90,k4_xboole_0(X90,X89)))
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f34538])).

fof(f1894,plain,(
    ! [X19,X20,X18] :
      ( k3_enumset1(X18,X18,X18,X18,X18) = k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),k4_xboole_0(X20,k4_xboole_0(X20,k3_enumset1(X18,X18,X18,X18,X19))))
      | r2_hidden(X19,k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),X20))
      | ~ r2_hidden(X18,k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),X20)) ) ),
    inference(superposition,[],[f84,f80])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f41,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f74,f41,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f72])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f73])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f110,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f61280,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_81 ),
    inference(avatar_contradiction_clause,[],[f61264])).

fof(f61264,plain,
    ( $false
    | spl5_1
    | spl5_2
    | ~ spl5_3
    | ~ spl5_81 ),
    inference(unit_resulting_resolution,[],[f115,f102,f61033,f98])).

fof(f61033,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))
    | spl5_1
    | ~ spl5_3
    | ~ spl5_81 ),
    inference(trivial_inequality_removal,[],[f60809])).

fof(f60809,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))
    | spl5_1
    | ~ spl5_3
    | ~ spl5_81 ),
    inference(superposition,[],[f32702,f59432])).

fof(f59432,plain,
    ( ! [X10,X11] :
        ( k3_enumset1(X10,X10,X10,X10,X10) = k4_xboole_0(k3_enumset1(X10,X10,X10,X10,X10),X11)
        | ~ r2_hidden(X10,k4_xboole_0(k3_enumset1(X10,X10,X10,X10,X10),X11)) )
    | ~ spl5_81 ),
    inference(forward_demodulation,[],[f1838,f34539])).

fof(f1838,plain,(
    ! [X10,X11] :
      ( k3_enumset1(X10,X10,X10,X10,X10) = k4_xboole_0(k3_enumset1(X10,X10,X10,X10,X10),k4_xboole_0(X11,k4_xboole_0(X11,k3_enumset1(X10,X10,X10,X10,X10))))
      | ~ r2_hidden(X10,k4_xboole_0(k3_enumset1(X10,X10,X10,X10,X10),X11)) ) ),
    inference(superposition,[],[f97,f80])).

fof(f97,plain,(
    ! [X2,X1] :
      ( k3_enumset1(X2,X2,X2,X2,X2) = k4_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k4_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X1))
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)) ) ),
    inference(definition_unfolding,[],[f50,f74,f41,f73])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f32702,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)
    | spl5_1
    | ~ spl5_3 ),
    inference(superposition,[],[f110,f119])).

fof(f119,plain,
    ( sK0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f102,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f34624,plain,
    ( spl5_81
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f34623,f1124,f34538])).

fof(f1124,plain,
    ( spl5_12
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f34623,plain,(
    ! [X50,X49] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k4_xboole_0(X49,k4_xboole_0(X50,k4_xboole_0(X50,X49))) = k4_xboole_0(X49,X50) ) ),
    inference(forward_demodulation,[],[f34622,f518])).

fof(f518,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f292,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f292,plain,(
    ! [X13] :
      ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13))
      | k1_xboole_0 = k4_xboole_0(k1_xboole_0,X13) ) ),
    inference(forward_demodulation,[],[f281,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f281,plain,(
    ! [X13] :
      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X13)
      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13)) ) ),
    inference(superposition,[],[f75,f239])).

fof(f239,plain,(
    ! [X6] :
      ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)
      | ~ r1_tarski(k1_xboole_0,X6) ) ),
    inference(superposition,[],[f172,f36])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f75,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34622,plain,(
    ! [X50,X49] :
      ( k4_xboole_0(X49,k4_xboole_0(X50,k4_xboole_0(X50,X49))) = k4_xboole_0(X49,X50)
      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X49,X50))) ) ),
    inference(forward_demodulation,[],[f34621,f22265])).

fof(f22265,plain,(
    ! [X169,X168] : k4_xboole_0(X168,X169) = k4_xboole_0(X168,k4_xboole_0(X168,k4_xboole_0(X168,X169))) ),
    inference(forward_demodulation,[],[f22131,f13039])).

fof(f13039,plain,(
    ! [X43,X44] : k4_xboole_0(X43,X44) = k4_xboole_0(X43,k4_xboole_0(X43,k5_xboole_0(X44,X43))) ),
    inference(forward_demodulation,[],[f13038,f75])).

fof(f13038,plain,(
    ! [X43,X44] : k5_xboole_0(X43,k4_xboole_0(X43,k4_xboole_0(X43,X44))) = k4_xboole_0(X43,k4_xboole_0(X43,k5_xboole_0(X44,X43))) ),
    inference(forward_demodulation,[],[f13037,f80])).

fof(f13037,plain,(
    ! [X43,X44] : k5_xboole_0(X43,k4_xboole_0(X43,k4_xboole_0(X43,X44))) = k4_xboole_0(k5_xboole_0(X44,X43),k4_xboole_0(k5_xboole_0(X44,X43),X43)) ),
    inference(forward_demodulation,[],[f13036,f1445])).

fof(f1445,plain,(
    ! [X24,X25] : k5_xboole_0(X25,X24) = k5_xboole_0(X24,X25) ),
    inference(forward_demodulation,[],[f1408,f996])).

fof(f996,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f956,f36])).

fof(f956,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f640,f626])).

fof(f626,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f611,f587])).

fof(f587,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(forward_demodulation,[],[f574,f36])).

fof(f574,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f75,f532])).

fof(f532,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f518,f80])).

fof(f611,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f75,f590])).

fof(f590,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f532,f587])).

fof(f640,plain,(
    ! [X14,X15] : k5_xboole_0(X14,k5_xboole_0(X14,X15)) = k5_xboole_0(k1_xboole_0,X15) ),
    inference(superposition,[],[f47,f626])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1408,plain,(
    ! [X24,X25] : k5_xboole_0(X24,X25) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X25),X24) ),
    inference(superposition,[],[f1341,f640])).

fof(f1341,plain,(
    ! [X23,X22] : k5_xboole_0(k5_xboole_0(X23,X22),X23) = X22 ),
    inference(superposition,[],[f1258,f1258])).

fof(f1258,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3 ),
    inference(superposition,[],[f1006,f996])).

fof(f1006,plain,(
    ! [X21,X20] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X21,k5_xboole_0(X20,X21))) = X20 ),
    inference(forward_demodulation,[],[f968,f36])).

fof(f968,plain,(
    ! [X21,X20] : k5_xboole_0(X20,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X21,k5_xboole_0(X20,X21))) ),
    inference(superposition,[],[f640,f632])).

fof(f632,plain,(
    ! [X8,X7] : k1_xboole_0 = k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X8))) ),
    inference(superposition,[],[f626,f47])).

fof(f13036,plain,(
    ! [X43,X44] : k4_xboole_0(k5_xboole_0(X44,X43),k4_xboole_0(k5_xboole_0(X44,X43),X43)) = k5_xboole_0(k4_xboole_0(X43,k4_xboole_0(X43,X44)),X43) ),
    inference(forward_demodulation,[],[f12584,f587])).

fof(f12584,plain,(
    ! [X43,X44] : k4_xboole_0(k5_xboole_0(X44,X43),k4_xboole_0(k5_xboole_0(X44,X43),k4_xboole_0(X43,k1_xboole_0))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),X44)),k4_xboole_0(X43,k1_xboole_0)) ),
    inference(superposition,[],[f1035,f532])).

fof(f1035,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k5_xboole_0(X3,X5),k4_xboole_0(k5_xboole_0(X3,X5),X4)) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),k4_xboole_0(X5,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f82,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(definition_unfolding,[],[f48,f41,f41,f41])).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f22131,plain,(
    ! [X169,X168] : k4_xboole_0(X168,k4_xboole_0(X168,k5_xboole_0(X169,X168))) = k4_xboole_0(X168,k4_xboole_0(X168,k4_xboole_0(X168,X169))) ),
    inference(superposition,[],[f14219,f20787])).

fof(f20787,plain,(
    ! [X204,X203] : k4_xboole_0(X203,X204) = k5_xboole_0(X203,k4_xboole_0(X203,k5_xboole_0(X204,X203))) ),
    inference(forward_demodulation,[],[f20786,f996])).

fof(f20786,plain,(
    ! [X204,X203] : k5_xboole_0(X203,k4_xboole_0(X203,k5_xboole_0(X204,X203))) = k4_xboole_0(X203,k5_xboole_0(k1_xboole_0,X204)) ),
    inference(forward_demodulation,[],[f20590,f640])).

fof(f20590,plain,(
    ! [X204,X203] : k4_xboole_0(X203,k5_xboole_0(X203,k5_xboole_0(X203,X204))) = k5_xboole_0(X203,k4_xboole_0(X203,k5_xboole_0(X204,X203))) ),
    inference(superposition,[],[f18908,f20091])).

fof(f20091,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k5_xboole_0(X18,X19)) = k4_xboole_0(X18,k5_xboole_0(X19,X18)) ),
    inference(superposition,[],[f18908,f17174])).

fof(f17174,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(superposition,[],[f75,f13039])).

fof(f18908,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f75,f14219])).

fof(f14219,plain,(
    ! [X43,X44] : k4_xboole_0(X43,X44) = k4_xboole_0(X43,k4_xboole_0(X43,k5_xboole_0(X43,X44))) ),
    inference(forward_demodulation,[],[f14218,f75])).

fof(f14218,plain,(
    ! [X43,X44] : k5_xboole_0(X43,k4_xboole_0(X43,k4_xboole_0(X43,X44))) = k4_xboole_0(X43,k4_xboole_0(X43,k5_xboole_0(X43,X44))) ),
    inference(forward_demodulation,[],[f14217,f587])).

fof(f14217,plain,(
    ! [X43,X44] : k5_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),X44))) = k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),k5_xboole_0(X43,X44))) ),
    inference(forward_demodulation,[],[f13812,f80])).

fof(f13812,plain,(
    ! [X43,X44] : k5_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),X44))) = k4_xboole_0(k5_xboole_0(X43,X44),k4_xboole_0(k5_xboole_0(X43,X44),k4_xboole_0(X43,k1_xboole_0))) ),
    inference(superposition,[],[f1059,f532])).

fof(f1059,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k5_xboole_0(X5,X3),k4_xboole_0(k5_xboole_0(X5,X3),X4)) = k5_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),k4_xboole_0(X4,k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f82,f80])).

fof(f34621,plain,(
    ! [X50,X49] :
      ( k4_xboole_0(X49,k4_xboole_0(X50,k4_xboole_0(X50,X49))) = k4_xboole_0(X49,k4_xboole_0(X49,k4_xboole_0(X49,X50)))
      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X49,X50))) ) ),
    inference(forward_demodulation,[],[f33558,f36])).

fof(f33558,plain,(
    ! [X50,X49] :
      ( k4_xboole_0(X49,k4_xboole_0(X50,k4_xboole_0(X50,X49))) = k4_xboole_0(k5_xboole_0(X49,k1_xboole_0),k4_xboole_0(k5_xboole_0(X49,k1_xboole_0),k4_xboole_0(X49,X50)))
      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X49,X50))) ) ),
    inference(superposition,[],[f266,f1024])).

fof(f1024,plain,(
    ! [X14,X15,X13] : k4_xboole_0(k5_xboole_0(X13,X15),k4_xboole_0(k5_xboole_0(X13,X15),k4_xboole_0(X13,X14))) = k5_xboole_0(k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X14,X13))),k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X13,X14)))) ),
    inference(superposition,[],[f82,f80])).

fof(f266,plain,(
    ! [X23,X22] :
      ( k5_xboole_0(X23,k4_xboole_0(k1_xboole_0,X22)) = X23
      | ~ r1_tarski(k1_xboole_0,X22) ) ),
    inference(forward_demodulation,[],[f260,f36])).

fof(f260,plain,(
    ! [X23,X22] :
      ( k5_xboole_0(X23,k1_xboole_0) = k5_xboole_0(X23,k4_xboole_0(k1_xboole_0,X22))
      | ~ r1_tarski(k1_xboole_0,X22) ) ),
    inference(superposition,[],[f135,f172])).

fof(f135,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f47,f36])).

fof(f20426,plain,
    ( spl5_3
    | ~ spl5_64 ),
    inference(avatar_contradiction_clause,[],[f20418])).

fof(f20418,plain,
    ( $false
    | spl5_3
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f120,f120,f120,f20416,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f68,f72])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20416,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f20414])).

fof(f20414,plain,
    ( spl5_64
  <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f120,plain,
    ( sK0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f20417,plain,
    ( spl5_64
    | spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f20404,f109,f123,f20414])).

fof(f20404,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f18534,f102])).

fof(f18534,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | r2_hidden(X2,sK2)
        | r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) )
    | ~ spl5_1 ),
    inference(superposition,[],[f98,f111])).

fof(f111,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f18818,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f18806])).

fof(f18806,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f114,f106,f18535])).

fof(f18535,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl5_1 ),
    inference(superposition,[],[f99,f111])).

fof(f106,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f1182,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f1177])).

fof(f1177,plain,
    ( $false
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f35,f1126])).

fof(f1126,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f1124])).

fof(f127,plain,
    ( spl5_1
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f79,f123,f118,f109])).

fof(f79,plain,
    ( r2_hidden(sK1,sK2)
    | sK0 = sK1
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f31,f74,f73])).

fof(f31,plain,
    ( r2_hidden(sK1,sK2)
    | sK0 = sK1
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f126,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f78,f113,f123,f109])).

fof(f78,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f32,f74,f73])).

fof(f32,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f121,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f77,f113,f118,f109])).

fof(f77,plain,
    ( r2_hidden(sK0,sK2)
    | sK0 != sK1
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f33,f74,f73])).

fof(f33,plain,
    ( r2_hidden(sK0,sK2)
    | sK0 != sK1
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f76,f113,f109])).

fof(f76,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f34,f74,f73])).

fof(f34,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (6321)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.50  % (6305)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (6303)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (6309)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (6307)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (6314)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (6325)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (6306)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (6310)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.54  % (6326)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.54  % (6318)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.54  % (6330)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.55  % (6322)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.55  % (6311)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.55  % (6323)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.55  % (6315)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.46/0.55  % (6312)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.46/0.56  % (6332)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.46/0.56  % (6324)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.46/0.56  % (6331)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.46/0.56  % (6313)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.46/0.56  % (6308)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.46/0.57  % (6316)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.57  % (6329)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.46/0.57  % (6327)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.46/0.57  % (6304)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.46/0.57  % (6328)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.46/0.58  % (6317)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.46/0.58  % (6319)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.58  % (6319)Refutation not found, incomplete strategy% (6319)------------------------------
% 1.46/0.58  % (6319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (6319)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (6319)Memory used [KB]: 10618
% 1.46/0.58  % (6319)Time elapsed: 0.166 s
% 1.46/0.58  % (6319)------------------------------
% 1.46/0.58  % (6319)------------------------------
% 1.46/0.59  % (6320)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.59  % (6313)Refutation not found, incomplete strategy% (6313)------------------------------
% 1.46/0.59  % (6313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.59  % (6313)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.59  
% 1.46/0.59  % (6313)Memory used [KB]: 10874
% 1.46/0.59  % (6313)Time elapsed: 0.127 s
% 1.46/0.59  % (6313)------------------------------
% 1.46/0.59  % (6313)------------------------------
% 2.42/0.69  % (6306)Refutation not found, incomplete strategy% (6306)------------------------------
% 2.42/0.69  % (6306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.42/0.69  % (6306)Termination reason: Refutation not found, incomplete strategy
% 2.42/0.69  
% 2.42/0.69  % (6306)Memory used [KB]: 6268
% 2.42/0.69  % (6306)Time elapsed: 0.260 s
% 2.42/0.69  % (6306)------------------------------
% 2.42/0.69  % (6306)------------------------------
% 2.42/0.72  % (6334)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.06/0.77  % (6333)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.43/0.84  % (6327)Time limit reached!
% 3.43/0.84  % (6327)------------------------------
% 3.43/0.84  % (6327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.43/0.84  % (6327)Termination reason: Time limit
% 3.43/0.84  % (6327)Termination phase: Saturation
% 3.43/0.84  
% 3.43/0.84  % (6327)Memory used [KB]: 12537
% 3.43/0.84  % (6327)Time elapsed: 0.400 s
% 3.43/0.84  % (6327)------------------------------
% 3.43/0.84  % (6327)------------------------------
% 3.67/0.86  % (6335)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.67/0.87  % (6305)Time limit reached!
% 3.67/0.87  % (6305)------------------------------
% 3.67/0.87  % (6305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.67/0.87  % (6305)Termination reason: Time limit
% 3.67/0.87  
% 3.67/0.87  % (6305)Memory used [KB]: 6780
% 3.67/0.87  % (6305)Time elapsed: 0.454 s
% 3.67/0.87  % (6305)------------------------------
% 3.67/0.87  % (6305)------------------------------
% 3.67/0.91  % (6309)Time limit reached!
% 3.67/0.91  % (6309)------------------------------
% 3.67/0.91  % (6309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.67/0.91  % (6309)Termination reason: Time limit
% 3.67/0.91  
% 3.67/0.91  % (6309)Memory used [KB]: 15351
% 3.67/0.91  % (6309)Time elapsed: 0.505 s
% 3.67/0.91  % (6309)------------------------------
% 3.67/0.91  % (6309)------------------------------
% 3.67/0.93  % (6336)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.21/0.94  % (6317)Time limit reached!
% 4.21/0.94  % (6317)------------------------------
% 4.21/0.94  % (6317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/0.94  % (6317)Termination reason: Time limit
% 4.21/0.94  
% 4.21/0.94  % (6317)Memory used [KB]: 3326
% 4.21/0.94  % (6317)Time elapsed: 0.512 s
% 4.21/0.94  % (6317)------------------------------
% 4.21/0.94  % (6317)------------------------------
% 4.21/0.94  % (6332)Time limit reached!
% 4.21/0.94  % (6332)------------------------------
% 4.21/0.94  % (6332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/0.94  % (6332)Termination reason: Time limit
% 4.21/0.94  
% 4.21/0.94  % (6332)Memory used [KB]: 2686
% 4.21/0.94  % (6332)Time elapsed: 0.503 s
% 4.21/0.94  % (6332)------------------------------
% 4.21/0.94  % (6332)------------------------------
% 4.93/1.05  % (6310)Time limit reached!
% 4.93/1.05  % (6310)------------------------------
% 4.93/1.05  % (6310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.06  % (6338)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.93/1.06  % (6310)Termination reason: Time limit
% 4.93/1.06  
% 4.93/1.06  % (6310)Memory used [KB]: 4989
% 4.93/1.06  % (6310)Time elapsed: 0.629 s
% 4.93/1.06  % (6310)------------------------------
% 4.93/1.06  % (6310)------------------------------
% 5.59/1.07  % (6337)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.59/1.08  % (6337)Refutation not found, incomplete strategy% (6337)------------------------------
% 5.59/1.08  % (6337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.59/1.08  % (6337)Termination reason: Refutation not found, incomplete strategy
% 5.59/1.08  
% 5.59/1.08  % (6337)Memory used [KB]: 10746
% 5.59/1.08  % (6337)Time elapsed: 0.152 s
% 5.59/1.08  % (6337)------------------------------
% 5.59/1.08  % (6337)------------------------------
% 5.59/1.09  % (6339)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.59/1.10  % (6340)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.29/1.23  % (6341)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.79/1.24  % (6304)Time limit reached!
% 6.79/1.24  % (6304)------------------------------
% 6.79/1.24  % (6304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.79/1.24  % (6304)Termination reason: Time limit
% 6.79/1.24  
% 6.79/1.24  % (6304)Memory used [KB]: 3965
% 6.79/1.24  % (6304)Time elapsed: 0.824 s
% 6.79/1.24  % (6304)------------------------------
% 6.79/1.24  % (6304)------------------------------
% 6.79/1.26  % (6342)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 7.80/1.37  % (6343)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 8.28/1.45  % (6315)Time limit reached!
% 8.28/1.45  % (6315)------------------------------
% 8.28/1.45  % (6315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.28/1.45  % (6315)Termination reason: Time limit
% 8.28/1.45  
% 8.28/1.45  % (6315)Memory used [KB]: 13560
% 8.28/1.45  % (6315)Time elapsed: 1.042 s
% 8.28/1.45  % (6315)------------------------------
% 8.28/1.45  % (6315)------------------------------
% 8.52/1.49  % (6330)Time limit reached!
% 8.52/1.49  % (6330)------------------------------
% 8.52/1.49  % (6330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.52/1.49  % (6330)Termination reason: Time limit
% 8.52/1.49  % (6330)Termination phase: Saturation
% 8.52/1.49  
% 8.52/1.49  % (6330)Memory used [KB]: 9850
% 8.52/1.49  % (6330)Time elapsed: 1.0000 s
% 8.52/1.49  % (6330)------------------------------
% 8.52/1.49  % (6330)------------------------------
% 9.02/1.56  % (6335)Time limit reached!
% 9.02/1.56  % (6335)------------------------------
% 9.02/1.56  % (6335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.02/1.56  % (6335)Termination reason: Time limit
% 9.02/1.56  
% 9.02/1.56  % (6335)Memory used [KB]: 12920
% 9.02/1.56  % (6335)Time elapsed: 0.830 s
% 9.02/1.56  % (6335)------------------------------
% 9.02/1.56  % (6335)------------------------------
% 9.02/1.57  % (6339)Time limit reached!
% 9.02/1.57  % (6339)------------------------------
% 9.02/1.57  % (6339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.02/1.57  % (6339)Termination reason: Time limit
% 9.02/1.57  % (6339)Termination phase: Saturation
% 9.02/1.57  
% 9.02/1.57  % (6339)Memory used [KB]: 16502
% 9.02/1.57  % (6339)Time elapsed: 0.600 s
% 9.02/1.57  % (6339)------------------------------
% 9.02/1.57  % (6339)------------------------------
% 9.02/1.58  % (6344)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.02/1.61  % (6345)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 9.02/1.64  % (6303)Time limit reached!
% 9.02/1.64  % (6303)------------------------------
% 9.02/1.64  % (6303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.02/1.64  % (6303)Termination reason: Time limit
% 9.02/1.64  % (6303)Termination phase: Saturation
% 9.02/1.64  
% 9.02/1.64  % (6303)Memory used [KB]: 10490
% 9.02/1.64  % (6303)Time elapsed: 1.200 s
% 9.02/1.64  % (6303)------------------------------
% 9.02/1.64  % (6303)------------------------------
% 10.35/1.71  % (6346)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 10.35/1.72  % (6308)Time limit reached!
% 10.35/1.72  % (6308)------------------------------
% 10.35/1.72  % (6308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.35/1.72  % (6308)Termination reason: Time limit
% 10.35/1.72  % (6308)Termination phase: Saturation
% 10.35/1.72  
% 10.35/1.72  % (6308)Memory used [KB]: 8827
% 10.35/1.72  % (6308)Time elapsed: 1.300 s
% 10.35/1.72  % (6308)------------------------------
% 10.35/1.72  % (6308)------------------------------
% 10.35/1.73  % (6346)Refutation not found, incomplete strategy% (6346)------------------------------
% 10.35/1.73  % (6346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.35/1.73  % (6346)Termination reason: Refutation not found, incomplete strategy
% 10.35/1.73  
% 10.35/1.73  % (6346)Memory used [KB]: 10746
% 10.35/1.73  % (6346)Time elapsed: 0.139 s
% 10.35/1.73  % (6346)------------------------------
% 10.35/1.73  % (6346)------------------------------
% 10.87/1.74  % (6347)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.07/1.81  % (6348)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 11.68/1.90  % (6350)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 11.68/1.90  % (6349)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 12.55/2.00  % (6342)Time limit reached!
% 12.55/2.00  % (6342)------------------------------
% 12.55/2.00  % (6342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.55/2.00  % (6342)Termination reason: Time limit
% 12.55/2.00  
% 12.55/2.00  % (6342)Memory used [KB]: 14328
% 12.55/2.00  % (6342)Time elapsed: 0.824 s
% 12.55/2.00  % (6342)------------------------------
% 12.55/2.00  % (6342)------------------------------
% 12.55/2.03  % (6329)Time limit reached!
% 12.55/2.03  % (6329)------------------------------
% 12.55/2.03  % (6329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.55/2.03  % (6329)Termination reason: Time limit
% 12.55/2.03  
% 12.55/2.03  % (6329)Memory used [KB]: 11641
% 12.55/2.03  % (6329)Time elapsed: 1.609 s
% 12.55/2.03  % (6329)------------------------------
% 12.55/2.03  % (6329)------------------------------
% 13.19/2.11  % (6348)Time limit reached!
% 13.19/2.11  % (6348)------------------------------
% 13.19/2.11  % (6348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.19/2.11  % (6348)Termination reason: Time limit
% 13.19/2.11  
% 13.19/2.11  % (6348)Memory used [KB]: 7291
% 13.19/2.11  % (6348)Time elapsed: 0.424 s
% 13.19/2.11  % (6348)------------------------------
% 13.19/2.11  % (6348)------------------------------
% 13.69/2.15  % (6351)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 13.69/2.16  % (6350)Time limit reached!
% 13.69/2.16  % (6350)------------------------------
% 13.69/2.16  % (6350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.69/2.16  % (6350)Termination reason: Time limit
% 13.69/2.16  
% 13.69/2.16  % (6350)Memory used [KB]: 7931
% 13.69/2.16  % (6350)Time elapsed: 0.408 s
% 13.69/2.16  % (6350)------------------------------
% 13.69/2.16  % (6350)------------------------------
% 14.28/2.18  % (6352)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 14.94/2.27  % (6353)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 14.94/2.29  % (6323)Time limit reached!
% 14.94/2.29  % (6323)------------------------------
% 14.94/2.29  % (6323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.94/2.29  % (6323)Termination reason: Time limit
% 14.94/2.29  
% 14.94/2.29  % (6323)Memory used [KB]: 23922
% 14.94/2.29  % (6323)Time elapsed: 1.855 s
% 14.94/2.29  % (6323)------------------------------
% 14.94/2.29  % (6323)------------------------------
% 15.34/2.32  % (6349)Time limit reached!
% 15.34/2.32  % (6349)------------------------------
% 15.34/2.32  % (6349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.34/2.32  % (6349)Termination reason: Time limit
% 15.34/2.32  
% 15.34/2.32  % (6349)Memory used [KB]: 11769
% 15.34/2.32  % (6349)Time elapsed: 0.501 s
% 15.34/2.32  % (6349)------------------------------
% 15.34/2.32  % (6349)------------------------------
% 16.14/2.45  % (6352)Time limit reached!
% 16.14/2.45  % (6352)------------------------------
% 16.14/2.45  % (6352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.14/2.45  % (6352)Termination reason: Time limit
% 16.14/2.45  
% 16.14/2.45  % (6352)Memory used [KB]: 2942
% 16.14/2.45  % (6352)Time elapsed: 0.403 s
% 16.14/2.45  % (6352)------------------------------
% 16.14/2.45  % (6352)------------------------------
% 17.38/2.56  % (6353)Time limit reached!
% 17.38/2.56  % (6353)------------------------------
% 17.38/2.56  % (6353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.38/2.56  % (6353)Termination reason: Time limit
% 17.38/2.56  
% 17.38/2.56  % (6353)Memory used [KB]: 8059
% 17.38/2.56  % (6353)Time elapsed: 0.421 s
% 17.38/2.56  % (6353)------------------------------
% 17.38/2.56  % (6353)------------------------------
% 19.07/2.82  % (6318)Time limit reached!
% 19.07/2.82  % (6318)------------------------------
% 19.07/2.82  % (6318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.07/2.82  % (6318)Termination reason: Time limit
% 19.07/2.82  % (6318)Termination phase: Saturation
% 19.07/2.82  
% 19.07/2.82  % (6318)Memory used [KB]: 15095
% 19.07/2.82  % (6318)Time elapsed: 2.400 s
% 19.07/2.82  % (6318)------------------------------
% 19.07/2.82  % (6318)------------------------------
% 25.19/3.55  % (6311)Time limit reached!
% 25.19/3.55  % (6311)------------------------------
% 25.19/3.55  % (6311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.19/3.55  % (6311)Termination reason: Time limit
% 25.19/3.55  
% 25.19/3.55  % (6311)Memory used [KB]: 20340
% 25.19/3.55  % (6311)Time elapsed: 3.122 s
% 25.19/3.55  % (6311)------------------------------
% 25.19/3.55  % (6311)------------------------------
% 25.19/3.56  % (6314)Time limit reached!
% 25.19/3.56  % (6314)------------------------------
% 25.19/3.56  % (6314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.19/3.56  % (6314)Termination reason: Time limit
% 25.19/3.56  
% 25.19/3.56  % (6314)Memory used [KB]: 24178
% 25.19/3.56  % (6314)Time elapsed: 3.138 s
% 25.19/3.56  % (6314)------------------------------
% 25.19/3.56  % (6314)------------------------------
% 26.35/3.73  % (6322)Time limit reached!
% 26.35/3.73  % (6322)------------------------------
% 26.35/3.73  % (6322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.35/3.73  % (6322)Termination reason: Time limit
% 26.35/3.73  
% 26.35/3.73  % (6322)Memory used [KB]: 16247
% 26.35/3.73  % (6322)Time elapsed: 3.319 s
% 26.35/3.73  % (6322)------------------------------
% 26.35/3.73  % (6322)------------------------------
% 29.55/4.09  % (6341)Time limit reached!
% 29.55/4.09  % (6341)------------------------------
% 29.55/4.09  % (6341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.55/4.09  % (6341)Termination reason: Time limit
% 29.55/4.09  % (6341)Termination phase: Saturation
% 29.55/4.09  
% 29.55/4.09  % (6341)Memory used [KB]: 29295
% 29.55/4.09  % (6341)Time elapsed: 3.0000 s
% 29.55/4.09  % (6341)------------------------------
% 29.55/4.09  % (6341)------------------------------
% 31.15/4.29  % (6340)Time limit reached!
% 31.15/4.29  % (6340)------------------------------
% 31.15/4.29  % (6340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.15/4.29  % (6340)Termination reason: Time limit
% 31.15/4.29  
% 31.15/4.29  % (6340)Memory used [KB]: 26865
% 31.15/4.29  % (6340)Time elapsed: 3.321 s
% 31.15/4.29  % (6340)------------------------------
% 31.15/4.29  % (6340)------------------------------
% 31.15/4.31  % (6336)Time limit reached!
% 31.15/4.31  % (6336)------------------------------
% 31.15/4.31  % (6336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.15/4.32  % (6336)Termination reason: Time limit
% 31.15/4.32  
% 31.15/4.32  % (6336)Memory used [KB]: 60254
% 31.15/4.32  % (6336)Time elapsed: 3.421 s
% 31.15/4.32  % (6336)------------------------------
% 31.15/4.32  % (6336)------------------------------
% 38.19/5.22  % (6320)Time limit reached!
% 38.19/5.22  % (6320)------------------------------
% 38.19/5.22  % (6320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 38.19/5.22  % (6320)Termination reason: Time limit
% 38.19/5.22  % (6320)Termination phase: Saturation
% 38.19/5.22  
% 38.19/5.22  % (6320)Memory used [KB]: 27632
% 38.19/5.22  % (6320)Time elapsed: 4.800 s
% 38.19/5.22  % (6320)------------------------------
% 38.19/5.22  % (6320)------------------------------
% 41.34/5.56  % (6316)Refutation found. Thanks to Tanya!
% 41.34/5.56  % SZS status Theorem for theBenchmark
% 41.34/5.56  % SZS output start Proof for theBenchmark
% 41.34/5.56  fof(f85159,plain,(
% 41.34/5.56    $false),
% 41.34/5.56    inference(avatar_sat_refutation,[],[f116,f121,f126,f127,f1182,f18818,f20417,f20426,f34624,f61280,f84925,f85105,f85157])).
% 41.34/5.56  fof(f85157,plain,(
% 41.34/5.56    ~spl5_4 | ~spl5_131),
% 41.34/5.56    inference(avatar_contradiction_clause,[],[f85134])).
% 41.34/5.56  fof(f85134,plain,(
% 41.34/5.56    $false | (~spl5_4 | ~spl5_131)),
% 41.34/5.56    inference(unit_resulting_resolution,[],[f124,f84924,f99])).
% 41.34/5.56  fof(f99,plain,(
% 41.34/5.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 41.34/5.56    inference(equality_resolution,[],[f57])).
% 41.34/5.56  fof(f57,plain,(
% 41.34/5.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 41.34/5.56    inference(cnf_transformation,[],[f2])).
% 41.34/5.56  fof(f2,axiom,(
% 41.34/5.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 41.34/5.56  fof(f84924,plain,(
% 41.34/5.56    r2_hidden(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~spl5_131),
% 41.34/5.56    inference(avatar_component_clause,[],[f84922])).
% 41.34/5.56  fof(f84922,plain,(
% 41.34/5.56    spl5_131 <=> r2_hidden(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 41.34/5.56    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).
% 41.34/5.56  fof(f124,plain,(
% 41.34/5.56    r2_hidden(sK1,sK2) | ~spl5_4),
% 41.34/5.56    inference(avatar_component_clause,[],[f123])).
% 41.34/5.56  fof(f123,plain,(
% 41.34/5.56    spl5_4 <=> r2_hidden(sK1,sK2)),
% 41.34/5.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 41.34/5.56  fof(f85105,plain,(
% 41.34/5.56    spl5_2 | spl5_130),
% 41.34/5.56    inference(avatar_contradiction_clause,[],[f85090])).
% 41.34/5.56  fof(f85090,plain,(
% 41.34/5.56    $false | (spl5_2 | spl5_130)),
% 41.34/5.56    inference(unit_resulting_resolution,[],[f115,f104,f84920,f98])).
% 41.34/5.56  fof(f98,plain,(
% 41.34/5.56    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 41.34/5.56    inference(equality_resolution,[],[f58])).
% 41.34/5.56  fof(f58,plain,(
% 41.34/5.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 41.34/5.56    inference(cnf_transformation,[],[f2])).
% 41.34/5.56  fof(f84920,plain,(
% 41.34/5.56    ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | spl5_130),
% 41.34/5.56    inference(avatar_component_clause,[],[f84918])).
% 41.34/5.56  fof(f84918,plain,(
% 41.34/5.56    spl5_130 <=> r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 41.34/5.56    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).
% 41.34/5.56  fof(f104,plain,(
% 41.34/5.56    ( ! [X4,X2,X0] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X4,X2))) )),
% 41.34/5.56    inference(equality_resolution,[],[f103])).
% 41.34/5.56  fof(f103,plain,(
% 41.34/5.56    ( ! [X4,X2,X0,X3] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X4,X2) != X3) )),
% 41.34/5.56    inference(equality_resolution,[],[f88])).
% 41.34/5.56  fof(f88,plain,(
% 41.34/5.56    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 41.34/5.56    inference(definition_unfolding,[],[f70,f72])).
% 41.34/5.56  fof(f72,plain,(
% 41.34/5.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 41.34/5.56    inference(definition_unfolding,[],[f46,f63])).
% 41.34/5.56  fof(f63,plain,(
% 41.34/5.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 41.34/5.56    inference(cnf_transformation,[],[f16])).
% 41.34/5.56  fof(f16,axiom,(
% 41.34/5.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 41.34/5.56  fof(f46,plain,(
% 41.34/5.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 41.34/5.56    inference(cnf_transformation,[],[f15])).
% 41.34/5.56  fof(f15,axiom,(
% 41.34/5.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 41.34/5.56  fof(f70,plain,(
% 41.34/5.56    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 41.34/5.56    inference(cnf_transformation,[],[f30])).
% 41.34/5.56  fof(f30,plain,(
% 41.34/5.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 41.34/5.56    inference(ennf_transformation,[],[f12])).
% 41.34/5.56  fof(f12,axiom,(
% 41.34/5.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 41.34/5.56  fof(f115,plain,(
% 41.34/5.56    ~r2_hidden(sK0,sK2) | spl5_2),
% 41.34/5.56    inference(avatar_component_clause,[],[f113])).
% 41.34/5.56  fof(f113,plain,(
% 41.34/5.56    spl5_2 <=> r2_hidden(sK0,sK2)),
% 41.34/5.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 41.34/5.56  fof(f84925,plain,(
% 41.34/5.56    ~spl5_130 | spl5_131 | spl5_1 | ~spl5_81),
% 41.34/5.56    inference(avatar_split_clause,[],[f84824,f34538,f109,f84922,f84918])).
% 41.34/5.56  fof(f109,plain,(
% 41.34/5.56    spl5_1 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 41.34/5.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 41.34/5.56  fof(f34538,plain,(
% 41.34/5.56    spl5_81 <=> ! [X89,X90] : k4_xboole_0(X89,X90) = k4_xboole_0(X89,k4_xboole_0(X90,k4_xboole_0(X90,X89)))),
% 41.34/5.56    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 41.34/5.56  fof(f84824,plain,(
% 41.34/5.56    r2_hidden(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | (spl5_1 | ~spl5_81)),
% 41.34/5.56    inference(trivial_inequality_removal,[],[f84507])).
% 41.34/5.56  fof(f84507,plain,(
% 41.34/5.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | r2_hidden(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | (spl5_1 | ~spl5_81)),
% 41.34/5.56    inference(superposition,[],[f110,f83587])).
% 41.34/5.56  fof(f83587,plain,(
% 41.34/5.56    ( ! [X19,X20,X18] : (k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),X20) = k3_enumset1(X18,X18,X18,X18,X18) | r2_hidden(X19,k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),X20)) | ~r2_hidden(X18,k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),X20))) ) | ~spl5_81),
% 41.34/5.56    inference(forward_demodulation,[],[f1894,f34539])).
% 41.34/5.56  fof(f34539,plain,(
% 41.34/5.56    ( ! [X90,X89] : (k4_xboole_0(X89,X90) = k4_xboole_0(X89,k4_xboole_0(X90,k4_xboole_0(X90,X89)))) ) | ~spl5_81),
% 41.34/5.56    inference(avatar_component_clause,[],[f34538])).
% 41.34/5.56  fof(f1894,plain,(
% 41.34/5.56    ( ! [X19,X20,X18] : (k3_enumset1(X18,X18,X18,X18,X18) = k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),k4_xboole_0(X20,k4_xboole_0(X20,k3_enumset1(X18,X18,X18,X18,X19)))) | r2_hidden(X19,k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),X20)) | ~r2_hidden(X18,k4_xboole_0(k3_enumset1(X18,X18,X18,X18,X19),X20))) )),
% 41.34/5.56    inference(superposition,[],[f84,f80])).
% 41.34/5.56  fof(f80,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 41.34/5.56    inference(definition_unfolding,[],[f38,f41,f41])).
% 41.34/5.56  fof(f41,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 41.34/5.56    inference(cnf_transformation,[],[f9])).
% 41.34/5.56  fof(f9,axiom,(
% 41.34/5.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 41.34/5.56  fof(f38,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 41.34/5.56    inference(cnf_transformation,[],[f1])).
% 41.34/5.56  fof(f1,axiom,(
% 41.34/5.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 41.34/5.56  fof(f84,plain,(
% 41.34/5.56    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 41.34/5.56    inference(definition_unfolding,[],[f49,f74,f41,f73])).
% 41.34/5.56  fof(f73,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 41.34/5.56    inference(definition_unfolding,[],[f39,f72])).
% 41.34/5.56  fof(f39,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 41.34/5.56    inference(cnf_transformation,[],[f14])).
% 41.34/5.56  fof(f14,axiom,(
% 41.34/5.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 41.34/5.56  fof(f74,plain,(
% 41.34/5.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 41.34/5.56    inference(definition_unfolding,[],[f37,f73])).
% 41.34/5.56  fof(f37,plain,(
% 41.34/5.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 41.34/5.56    inference(cnf_transformation,[],[f13])).
% 41.34/5.56  fof(f13,axiom,(
% 41.34/5.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 41.34/5.56  fof(f49,plain,(
% 41.34/5.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X2,X1) | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 41.34/5.56    inference(cnf_transformation,[],[f25])).
% 41.34/5.56  fof(f25,plain,(
% 41.34/5.56    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 41.34/5.56    inference(flattening,[],[f24])).
% 41.34/5.56  fof(f24,plain,(
% 41.34/5.56    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 41.34/5.56    inference(ennf_transformation,[],[f18])).
% 41.34/5.56  fof(f18,axiom,(
% 41.34/5.56    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 41.34/5.56  fof(f110,plain,(
% 41.34/5.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | spl5_1),
% 41.34/5.56    inference(avatar_component_clause,[],[f109])).
% 41.34/5.56  fof(f61280,plain,(
% 41.34/5.56    spl5_1 | spl5_2 | ~spl5_3 | ~spl5_81),
% 41.34/5.56    inference(avatar_contradiction_clause,[],[f61264])).
% 41.34/5.56  fof(f61264,plain,(
% 41.34/5.56    $false | (spl5_1 | spl5_2 | ~spl5_3 | ~spl5_81)),
% 41.34/5.56    inference(unit_resulting_resolution,[],[f115,f102,f61033,f98])).
% 41.34/5.56  fof(f61033,plain,(
% 41.34/5.56    ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)) | (spl5_1 | ~spl5_3 | ~spl5_81)),
% 41.34/5.56    inference(trivial_inequality_removal,[],[f60809])).
% 41.34/5.56  fof(f60809,plain,(
% 41.34/5.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)) | (spl5_1 | ~spl5_3 | ~spl5_81)),
% 41.34/5.56    inference(superposition,[],[f32702,f59432])).
% 41.34/5.56  fof(f59432,plain,(
% 41.34/5.56    ( ! [X10,X11] : (k3_enumset1(X10,X10,X10,X10,X10) = k4_xboole_0(k3_enumset1(X10,X10,X10,X10,X10),X11) | ~r2_hidden(X10,k4_xboole_0(k3_enumset1(X10,X10,X10,X10,X10),X11))) ) | ~spl5_81),
% 41.34/5.56    inference(forward_demodulation,[],[f1838,f34539])).
% 41.34/5.56  fof(f1838,plain,(
% 41.34/5.56    ( ! [X10,X11] : (k3_enumset1(X10,X10,X10,X10,X10) = k4_xboole_0(k3_enumset1(X10,X10,X10,X10,X10),k4_xboole_0(X11,k4_xboole_0(X11,k3_enumset1(X10,X10,X10,X10,X10)))) | ~r2_hidden(X10,k4_xboole_0(k3_enumset1(X10,X10,X10,X10,X10),X11))) )),
% 41.34/5.56    inference(superposition,[],[f97,f80])).
% 41.34/5.56  fof(f97,plain,(
% 41.34/5.56    ( ! [X2,X1] : (k3_enumset1(X2,X2,X2,X2,X2) = k4_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k4_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X1)) | ~r2_hidden(X2,X1)) )),
% 41.34/5.56    inference(equality_resolution,[],[f83])).
% 41.34/5.56  fof(f83,plain,(
% 41.34/5.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k3_enumset1(X0,X0,X0,X0,X0) = k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1))) )),
% 41.34/5.56    inference(definition_unfolding,[],[f50,f74,f41,f73])).
% 41.34/5.56  fof(f50,plain,(
% 41.34/5.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 41.34/5.56    inference(cnf_transformation,[],[f25])).
% 41.34/5.56  fof(f32702,plain,(
% 41.34/5.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) | (spl5_1 | ~spl5_3)),
% 41.34/5.56    inference(superposition,[],[f110,f119])).
% 41.34/5.56  fof(f119,plain,(
% 41.34/5.56    sK0 = sK1 | ~spl5_3),
% 41.34/5.56    inference(avatar_component_clause,[],[f118])).
% 41.34/5.56  fof(f118,plain,(
% 41.34/5.56    spl5_3 <=> sK0 = sK1),
% 41.34/5.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 41.34/5.56  fof(f102,plain,(
% 41.34/5.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4))) )),
% 41.34/5.56    inference(equality_resolution,[],[f101])).
% 41.34/5.56  fof(f101,plain,(
% 41.34/5.56    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X4) != X3) )),
% 41.34/5.56    inference(equality_resolution,[],[f87])).
% 41.34/5.56  fof(f87,plain,(
% 41.34/5.56    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 41.34/5.56    inference(definition_unfolding,[],[f71,f72])).
% 41.34/5.56  fof(f71,plain,(
% 41.34/5.56    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 41.34/5.56    inference(cnf_transformation,[],[f30])).
% 41.34/5.56  fof(f34624,plain,(
% 41.34/5.56    spl5_81 | ~spl5_12),
% 41.34/5.56    inference(avatar_split_clause,[],[f34623,f1124,f34538])).
% 41.34/5.56  fof(f1124,plain,(
% 41.34/5.56    spl5_12 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 41.34/5.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 41.34/5.56  fof(f34623,plain,(
% 41.34/5.56    ( ! [X50,X49] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | k4_xboole_0(X49,k4_xboole_0(X50,k4_xboole_0(X50,X49))) = k4_xboole_0(X49,X50)) )),
% 41.34/5.56    inference(forward_demodulation,[],[f34622,f518])).
% 41.34/5.56  fof(f518,plain,(
% 41.34/5.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 41.34/5.56    inference(resolution,[],[f292,f35])).
% 41.34/5.56  fof(f35,plain,(
% 41.34/5.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 41.34/5.56    inference(cnf_transformation,[],[f8])).
% 41.34/5.56  fof(f8,axiom,(
% 41.34/5.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 41.34/5.56  fof(f292,plain,(
% 41.34/5.56    ( ! [X13] : (~r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13)) | k1_xboole_0 = k4_xboole_0(k1_xboole_0,X13)) )),
% 41.34/5.56    inference(forward_demodulation,[],[f281,f36])).
% 41.34/5.56  fof(f36,plain,(
% 41.34/5.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 41.34/5.56    inference(cnf_transformation,[],[f10])).
% 41.34/5.56  fof(f10,axiom,(
% 41.34/5.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 41.34/5.56  fof(f281,plain,(
% 41.34/5.56    ( ! [X13] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X13) | ~r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13))) )),
% 41.34/5.56    inference(superposition,[],[f75,f239])).
% 41.34/5.56  fof(f239,plain,(
% 41.34/5.56    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) | ~r1_tarski(k1_xboole_0,X6)) )),
% 41.34/5.56    inference(superposition,[],[f172,f36])).
% 41.34/5.56  fof(f172,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 41.34/5.56    inference(superposition,[],[f75,f81])).
% 41.34/5.56  fof(f81,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 41.34/5.56    inference(definition_unfolding,[],[f42,f41])).
% 41.34/5.56  fof(f42,plain,(
% 41.34/5.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 41.34/5.56    inference(cnf_transformation,[],[f23])).
% 41.34/5.56  fof(f23,plain,(
% 41.34/5.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 41.34/5.56    inference(ennf_transformation,[],[f7])).
% 41.34/5.56  fof(f7,axiom,(
% 41.34/5.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 41.34/5.56  fof(f75,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 41.34/5.56    inference(definition_unfolding,[],[f40,f41])).
% 41.34/5.56  fof(f40,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 41.34/5.56    inference(cnf_transformation,[],[f5])).
% 41.34/5.56  fof(f5,axiom,(
% 41.34/5.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 41.34/5.56  fof(f34622,plain,(
% 41.34/5.56    ( ! [X50,X49] : (k4_xboole_0(X49,k4_xboole_0(X50,k4_xboole_0(X50,X49))) = k4_xboole_0(X49,X50) | ~r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X49,X50)))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f34621,f22265])).
% 41.34/5.56  fof(f22265,plain,(
% 41.34/5.56    ( ! [X169,X168] : (k4_xboole_0(X168,X169) = k4_xboole_0(X168,k4_xboole_0(X168,k4_xboole_0(X168,X169)))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f22131,f13039])).
% 41.34/5.56  fof(f13039,plain,(
% 41.34/5.56    ( ! [X43,X44] : (k4_xboole_0(X43,X44) = k4_xboole_0(X43,k4_xboole_0(X43,k5_xboole_0(X44,X43)))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f13038,f75])).
% 41.34/5.56  fof(f13038,plain,(
% 41.34/5.56    ( ! [X43,X44] : (k5_xboole_0(X43,k4_xboole_0(X43,k4_xboole_0(X43,X44))) = k4_xboole_0(X43,k4_xboole_0(X43,k5_xboole_0(X44,X43)))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f13037,f80])).
% 41.34/5.56  fof(f13037,plain,(
% 41.34/5.56    ( ! [X43,X44] : (k5_xboole_0(X43,k4_xboole_0(X43,k4_xboole_0(X43,X44))) = k4_xboole_0(k5_xboole_0(X44,X43),k4_xboole_0(k5_xboole_0(X44,X43),X43))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f13036,f1445])).
% 41.34/5.56  fof(f1445,plain,(
% 41.34/5.56    ( ! [X24,X25] : (k5_xboole_0(X25,X24) = k5_xboole_0(X24,X25)) )),
% 41.34/5.56    inference(forward_demodulation,[],[f1408,f996])).
% 41.34/5.56  fof(f996,plain,(
% 41.34/5.56    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 41.34/5.56    inference(forward_demodulation,[],[f956,f36])).
% 41.34/5.56  fof(f956,plain,(
% 41.34/5.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 41.34/5.56    inference(superposition,[],[f640,f626])).
% 41.34/5.56  fof(f626,plain,(
% 41.34/5.56    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 41.34/5.56    inference(forward_demodulation,[],[f611,f587])).
% 41.34/5.56  fof(f587,plain,(
% 41.34/5.56    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = X5) )),
% 41.34/5.56    inference(forward_demodulation,[],[f574,f36])).
% 41.34/5.56  fof(f574,plain,(
% 41.34/5.56    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0)) )),
% 41.34/5.56    inference(superposition,[],[f75,f532])).
% 41.34/5.56  fof(f532,plain,(
% 41.34/5.56    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) )),
% 41.34/5.56    inference(superposition,[],[f518,f80])).
% 41.34/5.56  fof(f611,plain,(
% 41.34/5.56    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) )),
% 41.34/5.56    inference(superposition,[],[f75,f590])).
% 41.34/5.56  fof(f590,plain,(
% 41.34/5.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 41.34/5.56    inference(superposition,[],[f532,f587])).
% 41.34/5.56  fof(f640,plain,(
% 41.34/5.56    ( ! [X14,X15] : (k5_xboole_0(X14,k5_xboole_0(X14,X15)) = k5_xboole_0(k1_xboole_0,X15)) )),
% 41.34/5.56    inference(superposition,[],[f47,f626])).
% 41.34/5.56  fof(f47,plain,(
% 41.34/5.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 41.34/5.56    inference(cnf_transformation,[],[f11])).
% 41.34/5.56  fof(f11,axiom,(
% 41.34/5.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 41.34/5.56  fof(f1408,plain,(
% 41.34/5.56    ( ! [X24,X25] : (k5_xboole_0(X24,X25) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X25),X24)) )),
% 41.34/5.56    inference(superposition,[],[f1341,f640])).
% 41.34/5.56  fof(f1341,plain,(
% 41.34/5.56    ( ! [X23,X22] : (k5_xboole_0(k5_xboole_0(X23,X22),X23) = X22) )),
% 41.34/5.56    inference(superposition,[],[f1258,f1258])).
% 41.34/5.56  fof(f1258,plain,(
% 41.34/5.56    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3) )),
% 41.34/5.56    inference(superposition,[],[f1006,f996])).
% 41.34/5.56  fof(f1006,plain,(
% 41.34/5.56    ( ! [X21,X20] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X21,k5_xboole_0(X20,X21))) = X20) )),
% 41.34/5.56    inference(forward_demodulation,[],[f968,f36])).
% 41.34/5.56  fof(f968,plain,(
% 41.34/5.56    ( ! [X21,X20] : (k5_xboole_0(X20,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X21,k5_xboole_0(X20,X21)))) )),
% 41.34/5.56    inference(superposition,[],[f640,f632])).
% 41.34/5.56  fof(f632,plain,(
% 41.34/5.56    ( ! [X8,X7] : (k1_xboole_0 = k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X8)))) )),
% 41.34/5.56    inference(superposition,[],[f626,f47])).
% 41.34/5.56  fof(f13036,plain,(
% 41.34/5.56    ( ! [X43,X44] : (k4_xboole_0(k5_xboole_0(X44,X43),k4_xboole_0(k5_xboole_0(X44,X43),X43)) = k5_xboole_0(k4_xboole_0(X43,k4_xboole_0(X43,X44)),X43)) )),
% 41.34/5.56    inference(forward_demodulation,[],[f12584,f587])).
% 41.34/5.56  fof(f12584,plain,(
% 41.34/5.56    ( ! [X43,X44] : (k4_xboole_0(k5_xboole_0(X44,X43),k4_xboole_0(k5_xboole_0(X44,X43),k4_xboole_0(X43,k1_xboole_0))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),X44)),k4_xboole_0(X43,k1_xboole_0))) )),
% 41.34/5.56    inference(superposition,[],[f1035,f532])).
% 41.34/5.56  fof(f1035,plain,(
% 41.34/5.56    ( ! [X4,X5,X3] : (k4_xboole_0(k5_xboole_0(X3,X5),k4_xboole_0(k5_xboole_0(X3,X5),X4)) = k5_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),k4_xboole_0(X5,k4_xboole_0(X5,X4)))) )),
% 41.34/5.56    inference(superposition,[],[f82,f80])).
% 41.34/5.56  fof(f82,plain,(
% 41.34/5.56    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1))) )),
% 41.34/5.56    inference(definition_unfolding,[],[f48,f41,f41,f41])).
% 41.34/5.56  fof(f48,plain,(
% 41.34/5.56    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 41.34/5.56    inference(cnf_transformation,[],[f6])).
% 41.34/5.56  fof(f6,axiom,(
% 41.34/5.56    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 41.34/5.56  fof(f22131,plain,(
% 41.34/5.56    ( ! [X169,X168] : (k4_xboole_0(X168,k4_xboole_0(X168,k5_xboole_0(X169,X168))) = k4_xboole_0(X168,k4_xboole_0(X168,k4_xboole_0(X168,X169)))) )),
% 41.34/5.56    inference(superposition,[],[f14219,f20787])).
% 41.34/5.56  fof(f20787,plain,(
% 41.34/5.56    ( ! [X204,X203] : (k4_xboole_0(X203,X204) = k5_xboole_0(X203,k4_xboole_0(X203,k5_xboole_0(X204,X203)))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f20786,f996])).
% 41.34/5.56  fof(f20786,plain,(
% 41.34/5.56    ( ! [X204,X203] : (k5_xboole_0(X203,k4_xboole_0(X203,k5_xboole_0(X204,X203))) = k4_xboole_0(X203,k5_xboole_0(k1_xboole_0,X204))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f20590,f640])).
% 41.34/5.56  fof(f20590,plain,(
% 41.34/5.56    ( ! [X204,X203] : (k4_xboole_0(X203,k5_xboole_0(X203,k5_xboole_0(X203,X204))) = k5_xboole_0(X203,k4_xboole_0(X203,k5_xboole_0(X204,X203)))) )),
% 41.34/5.56    inference(superposition,[],[f18908,f20091])).
% 41.34/5.56  fof(f20091,plain,(
% 41.34/5.56    ( ! [X19,X18] : (k4_xboole_0(X18,k5_xboole_0(X18,X19)) = k4_xboole_0(X18,k5_xboole_0(X19,X18))) )),
% 41.34/5.56    inference(superposition,[],[f18908,f17174])).
% 41.34/5.56  fof(f17174,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,X0))) )),
% 41.34/5.56    inference(superposition,[],[f75,f13039])).
% 41.34/5.56  fof(f18908,plain,(
% 41.34/5.56    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k5_xboole_0(X1,X2))) )),
% 41.34/5.56    inference(superposition,[],[f75,f14219])).
% 41.34/5.56  fof(f14219,plain,(
% 41.34/5.56    ( ! [X43,X44] : (k4_xboole_0(X43,X44) = k4_xboole_0(X43,k4_xboole_0(X43,k5_xboole_0(X43,X44)))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f14218,f75])).
% 41.34/5.56  fof(f14218,plain,(
% 41.34/5.56    ( ! [X43,X44] : (k5_xboole_0(X43,k4_xboole_0(X43,k4_xboole_0(X43,X44))) = k4_xboole_0(X43,k4_xboole_0(X43,k5_xboole_0(X43,X44)))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f14217,f587])).
% 41.34/5.56  fof(f14217,plain,(
% 41.34/5.56    ( ! [X43,X44] : (k5_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),X44))) = k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),k5_xboole_0(X43,X44)))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f13812,f80])).
% 41.34/5.56  fof(f13812,plain,(
% 41.34/5.56    ( ! [X43,X44] : (k5_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),k4_xboole_0(k4_xboole_0(X43,k1_xboole_0),X44))) = k4_xboole_0(k5_xboole_0(X43,X44),k4_xboole_0(k5_xboole_0(X43,X44),k4_xboole_0(X43,k1_xboole_0)))) )),
% 41.34/5.56    inference(superposition,[],[f1059,f532])).
% 41.34/5.56  fof(f1059,plain,(
% 41.34/5.56    ( ! [X4,X5,X3] : (k4_xboole_0(k5_xboole_0(X5,X3),k4_xboole_0(k5_xboole_0(X5,X3),X4)) = k5_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),k4_xboole_0(X4,k4_xboole_0(X4,X3)))) )),
% 41.34/5.56    inference(superposition,[],[f82,f80])).
% 41.34/5.56  fof(f34621,plain,(
% 41.34/5.56    ( ! [X50,X49] : (k4_xboole_0(X49,k4_xboole_0(X50,k4_xboole_0(X50,X49))) = k4_xboole_0(X49,k4_xboole_0(X49,k4_xboole_0(X49,X50))) | ~r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X49,X50)))) )),
% 41.34/5.56    inference(forward_demodulation,[],[f33558,f36])).
% 41.34/5.56  fof(f33558,plain,(
% 41.34/5.56    ( ! [X50,X49] : (k4_xboole_0(X49,k4_xboole_0(X50,k4_xboole_0(X50,X49))) = k4_xboole_0(k5_xboole_0(X49,k1_xboole_0),k4_xboole_0(k5_xboole_0(X49,k1_xboole_0),k4_xboole_0(X49,X50))) | ~r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X49,X50)))) )),
% 41.34/5.56    inference(superposition,[],[f266,f1024])).
% 41.34/5.56  fof(f1024,plain,(
% 41.34/5.56    ( ! [X14,X15,X13] : (k4_xboole_0(k5_xboole_0(X13,X15),k4_xboole_0(k5_xboole_0(X13,X15),k4_xboole_0(X13,X14))) = k5_xboole_0(k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X14,X13))),k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X13,X14))))) )),
% 41.34/5.56    inference(superposition,[],[f82,f80])).
% 41.34/5.56  fof(f266,plain,(
% 41.34/5.56    ( ! [X23,X22] : (k5_xboole_0(X23,k4_xboole_0(k1_xboole_0,X22)) = X23 | ~r1_tarski(k1_xboole_0,X22)) )),
% 41.34/5.56    inference(forward_demodulation,[],[f260,f36])).
% 41.34/5.56  fof(f260,plain,(
% 41.34/5.56    ( ! [X23,X22] : (k5_xboole_0(X23,k1_xboole_0) = k5_xboole_0(X23,k4_xboole_0(k1_xboole_0,X22)) | ~r1_tarski(k1_xboole_0,X22)) )),
% 41.34/5.56    inference(superposition,[],[f135,f172])).
% 41.34/5.56  fof(f135,plain,(
% 41.34/5.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 41.34/5.56    inference(superposition,[],[f47,f36])).
% 41.34/5.56  fof(f20426,plain,(
% 41.34/5.56    spl5_3 | ~spl5_64),
% 41.34/5.56    inference(avatar_contradiction_clause,[],[f20418])).
% 41.34/5.56  fof(f20418,plain,(
% 41.34/5.56    $false | (spl5_3 | ~spl5_64)),
% 41.34/5.56    inference(unit_resulting_resolution,[],[f120,f120,f120,f20416,f107])).
% 41.34/5.56  fof(f107,plain,(
% 41.34/5.56    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 41.34/5.56    inference(equality_resolution,[],[f90])).
% 41.34/5.56  fof(f90,plain,(
% 41.34/5.56    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 41.34/5.56    inference(definition_unfolding,[],[f68,f72])).
% 41.34/5.56  fof(f68,plain,(
% 41.34/5.56    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 41.34/5.56    inference(cnf_transformation,[],[f30])).
% 41.34/5.56  fof(f20416,plain,(
% 41.34/5.56    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl5_64),
% 41.34/5.56    inference(avatar_component_clause,[],[f20414])).
% 41.34/5.56  fof(f20414,plain,(
% 41.34/5.56    spl5_64 <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 41.34/5.56    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 41.34/5.56  fof(f120,plain,(
% 41.34/5.56    sK0 != sK1 | spl5_3),
% 41.34/5.56    inference(avatar_component_clause,[],[f118])).
% 41.34/5.56  fof(f20417,plain,(
% 41.34/5.56    spl5_64 | spl5_4 | ~spl5_1),
% 41.34/5.56    inference(avatar_split_clause,[],[f20404,f109,f123,f20414])).
% 41.34/5.56  fof(f20404,plain,(
% 41.34/5.56    r2_hidden(sK1,sK2) | r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl5_1),
% 41.34/5.56    inference(resolution,[],[f18534,f102])).
% 41.34/5.56  fof(f18534,plain,(
% 41.34/5.56    ( ! [X2] : (~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | r2_hidden(X2,sK2) | r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ) | ~spl5_1),
% 41.34/5.56    inference(superposition,[],[f98,f111])).
% 41.34/5.56  fof(f111,plain,(
% 41.34/5.56    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | ~spl5_1),
% 41.34/5.56    inference(avatar_component_clause,[],[f109])).
% 41.34/5.56  fof(f18818,plain,(
% 41.34/5.56    ~spl5_1 | ~spl5_2),
% 41.34/5.56    inference(avatar_contradiction_clause,[],[f18806])).
% 41.34/5.56  fof(f18806,plain,(
% 41.34/5.56    $false | (~spl5_1 | ~spl5_2)),
% 41.34/5.56    inference(unit_resulting_resolution,[],[f114,f106,f18535])).
% 41.34/5.56  fof(f18535,plain,(
% 41.34/5.56    ( ! [X3] : (~r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X3,sK2)) ) | ~spl5_1),
% 41.34/5.56    inference(superposition,[],[f99,f111])).
% 41.34/5.56  fof(f106,plain,(
% 41.34/5.56    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 41.34/5.56    inference(equality_resolution,[],[f105])).
% 41.34/5.56  fof(f105,plain,(
% 41.34/5.56    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 41.34/5.56    inference(equality_resolution,[],[f89])).
% 41.34/5.56  fof(f89,plain,(
% 41.34/5.56    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 41.34/5.56    inference(definition_unfolding,[],[f69,f72])).
% 41.34/5.56  fof(f69,plain,(
% 41.34/5.56    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 41.34/5.56    inference(cnf_transformation,[],[f30])).
% 41.34/5.56  fof(f114,plain,(
% 41.34/5.56    r2_hidden(sK0,sK2) | ~spl5_2),
% 41.34/5.56    inference(avatar_component_clause,[],[f113])).
% 41.34/5.56  fof(f1182,plain,(
% 41.34/5.56    spl5_12),
% 41.34/5.56    inference(avatar_contradiction_clause,[],[f1177])).
% 41.34/5.56  fof(f1177,plain,(
% 41.34/5.56    $false | spl5_12),
% 41.34/5.56    inference(unit_resulting_resolution,[],[f35,f1126])).
% 41.34/5.56  fof(f1126,plain,(
% 41.34/5.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl5_12),
% 41.34/5.56    inference(avatar_component_clause,[],[f1124])).
% 41.34/5.56  fof(f127,plain,(
% 41.34/5.56    spl5_1 | spl5_3 | spl5_4),
% 41.34/5.56    inference(avatar_split_clause,[],[f79,f123,f118,f109])).
% 41.34/5.56  fof(f79,plain,(
% 41.34/5.56    r2_hidden(sK1,sK2) | sK0 = sK1 | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 41.34/5.56    inference(definition_unfolding,[],[f31,f74,f73])).
% 41.34/5.56  fof(f31,plain,(
% 41.34/5.56    r2_hidden(sK1,sK2) | sK0 = sK1 | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 41.34/5.56    inference(cnf_transformation,[],[f22])).
% 41.34/5.56  fof(f22,plain,(
% 41.34/5.56    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 41.34/5.56    inference(ennf_transformation,[],[f21])).
% 41.34/5.56  fof(f21,negated_conjecture,(
% 41.34/5.56    ~! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 41.34/5.56    inference(negated_conjecture,[],[f20])).
% 41.34/5.56  fof(f20,conjecture,(
% 41.34/5.56    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 41.34/5.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 41.34/5.56  fof(f126,plain,(
% 41.34/5.56    ~spl5_1 | ~spl5_4 | spl5_2),
% 41.34/5.56    inference(avatar_split_clause,[],[f78,f113,f123,f109])).
% 41.34/5.56  fof(f78,plain,(
% 41.34/5.56    r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 41.34/5.56    inference(definition_unfolding,[],[f32,f74,f73])).
% 41.34/5.56  fof(f32,plain,(
% 41.34/5.56    r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 41.34/5.56    inference(cnf_transformation,[],[f22])).
% 41.34/5.56  fof(f121,plain,(
% 41.34/5.56    ~spl5_1 | ~spl5_3 | spl5_2),
% 41.34/5.56    inference(avatar_split_clause,[],[f77,f113,f118,f109])).
% 41.34/5.56  fof(f77,plain,(
% 41.34/5.56    r2_hidden(sK0,sK2) | sK0 != sK1 | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 41.34/5.56    inference(definition_unfolding,[],[f33,f74,f73])).
% 41.34/5.56  fof(f33,plain,(
% 41.34/5.56    r2_hidden(sK0,sK2) | sK0 != sK1 | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 41.34/5.56    inference(cnf_transformation,[],[f22])).
% 41.34/5.56  fof(f116,plain,(
% 41.34/5.56    spl5_1 | ~spl5_2),
% 41.34/5.56    inference(avatar_split_clause,[],[f76,f113,f109])).
% 41.34/5.56  fof(f76,plain,(
% 41.34/5.56    ~r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 41.34/5.56    inference(definition_unfolding,[],[f34,f74,f73])).
% 41.34/5.56  fof(f34,plain,(
% 41.34/5.56    ~r2_hidden(sK0,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 41.34/5.56    inference(cnf_transformation,[],[f22])).
% 41.34/5.56  % SZS output end Proof for theBenchmark
% 41.34/5.56  % (6316)------------------------------
% 41.34/5.56  % (6316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.34/5.56  % (6316)Termination reason: Refutation
% 41.34/5.56  
% 41.34/5.56  % (6316)Memory used [KB]: 62173
% 41.34/5.56  % (6316)Time elapsed: 5.122 s
% 41.34/5.56  % (6316)------------------------------
% 41.34/5.56  % (6316)------------------------------
% 41.34/5.57  % (6302)Success in time 5.196 s
%------------------------------------------------------------------------------
