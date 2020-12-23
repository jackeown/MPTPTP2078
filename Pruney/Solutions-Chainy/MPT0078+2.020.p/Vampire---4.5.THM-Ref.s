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
% DateTime   : Thu Dec  3 12:30:50 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 186 expanded)
%              Number of leaves         :   26 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  205 ( 378 expanded)
%              Number of equality atoms :   56 ( 128 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f938,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f63,f77,f293,f312,f317,f383,f453,f498,f549,f616,f929,f937])).

fof(f937,plain,
    ( spl5_1
    | ~ spl5_53
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f936,f912,f610,f39])).

fof(f39,plain,
    ( spl5_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f610,plain,
    ( spl5_53
  <=> sK0 = k2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f912,plain,
    ( spl5_68
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f936,plain,
    ( sK0 = sK2
    | ~ spl5_53
    | ~ spl5_68 ),
    inference(forward_demodulation,[],[f935,f612])).

fof(f612,plain,
    ( sK0 = k2_xboole_0(sK0,sK2)
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f610])).

fof(f935,plain,
    ( sK2 = k2_xboole_0(sK0,sK2)
    | ~ spl5_68 ),
    inference(resolution,[],[f914,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f914,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f912])).

fof(f929,plain,
    ( spl5_68
    | ~ spl5_6
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f928,f546,f71,f912])).

fof(f71,plain,
    ( spl5_6
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f546,plain,
    ( spl5_44
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f928,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl5_6
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f927,f548])).

fof(f548,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f546])).

fof(f927,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl5_6
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f905,f548])).

fof(f905,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f125,f96])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f91,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f91,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f66,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f125,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,k2_xboole_0(sK0,sK1))
        | r1_tarski(k4_xboole_0(X10,sK1),sK2) )
    | ~ spl5_6 ),
    inference(superposition,[],[f34,f73])).

fof(f73,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f616,plain,
    ( spl5_53
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f602,f495,f610])).

fof(f495,plain,
    ( spl5_42
  <=> sK0 = k2_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f602,plain,
    ( sK0 = k2_xboole_0(sK0,sK2)
    | ~ spl5_42 ),
    inference(superposition,[],[f27,f497])).

fof(f497,plain,
    ( sK0 = k2_xboole_0(sK2,sK0)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f495])).

fof(f549,plain,
    ( spl5_44
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f544,f314,f546])).

fof(f314,plain,
    ( spl5_26
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f544,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f526,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f526,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl5_26 ),
    inference(superposition,[],[f35,f316])).

fof(f316,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f314])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f498,plain,
    ( spl5_42
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f493,f450,f495])).

fof(f450,plain,
    ( spl5_38
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f493,plain,
    ( sK0 = k2_xboole_0(sK2,sK0)
    | ~ spl5_38 ),
    inference(resolution,[],[f452,f33])).

fof(f452,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f450])).

fof(f453,plain,
    ( spl5_38
    | ~ spl5_22
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f440,f380,f290,f450])).

fof(f290,plain,
    ( spl5_22
  <=> r1_tarski(k4_xboole_0(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f380,plain,
    ( spl5_30
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f440,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_22
    | ~ spl5_30 ),
    inference(backward_demodulation,[],[f292,f382])).

fof(f382,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f380])).

fof(f292,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK0)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f290])).

fof(f383,plain,
    ( spl5_30
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f378,f309,f380])).

fof(f309,plain,
    ( spl5_25
  <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f378,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f369,f24])).

fof(f369,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_25 ),
    inference(superposition,[],[f35,f311])).

fof(f311,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f309])).

fof(f317,plain,
    ( spl5_26
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f307,f49,f314])).

fof(f49,plain,
    ( spl5_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f307,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_3 ),
    inference(resolution,[],[f139,f51])).

fof(f51,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f37,f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f312,plain,
    ( spl5_25
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f306,f44,f309])).

fof(f44,plain,
    ( spl5_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f306,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f139,f46])).

fof(f46,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f293,plain,
    ( spl5_22
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f272,f60,f290])).

fof(f60,plain,
    ( spl5_5
  <=> r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f272,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f122,f62])).

fof(f62,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f122,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X3,k2_xboole_0(X2,X1))
      | r1_tarski(k4_xboole_0(X3,X1),X2) ) ),
    inference(superposition,[],[f34,f27])).

fof(f77,plain,
    ( spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f69,f54,f71])).

fof(f54,plain,
    ( spl5_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f69,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl5_4 ),
    inference(superposition,[],[f56,f27])).

fof(f56,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f63,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f58,f54,f60])).

fof(f58,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl5_4 ),
    inference(superposition,[],[f26,f56])).

fof(f57,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f20,f54])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f52,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (21258)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.57/0.56  % (21276)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.57  % (21260)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.57/0.57  % (21274)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.57/0.57  % (21256)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.57/0.57  % (21252)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.57/0.57  % (21266)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.57/0.57  % (21257)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.57/0.58  % (21260)Refutation not found, incomplete strategy% (21260)------------------------------
% 1.57/0.58  % (21260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (21268)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.57/0.58  % (21254)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.57/0.58  % (21260)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (21260)Memory used [KB]: 10618
% 1.57/0.58  % (21260)Time elapsed: 0.151 s
% 1.57/0.58  % (21260)------------------------------
% 1.57/0.58  % (21260)------------------------------
% 1.57/0.58  % (21254)Refutation not found, incomplete strategy% (21254)------------------------------
% 1.57/0.58  % (21254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (21254)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (21254)Memory used [KB]: 10618
% 1.57/0.58  % (21254)Time elapsed: 0.150 s
% 1.57/0.58  % (21254)------------------------------
% 1.57/0.58  % (21254)------------------------------
% 1.57/0.58  % (21274)Refutation not found, incomplete strategy% (21274)------------------------------
% 1.57/0.58  % (21274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (21275)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.57/0.59  % (21267)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.57/0.59  % (21274)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (21274)Memory used [KB]: 10746
% 1.57/0.59  % (21274)Time elapsed: 0.159 s
% 1.57/0.59  % (21274)------------------------------
% 1.57/0.59  % (21274)------------------------------
% 1.57/0.59  % (21267)Refutation not found, incomplete strategy% (21267)------------------------------
% 1.57/0.59  % (21267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (21267)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (21267)Memory used [KB]: 6140
% 1.57/0.59  % (21267)Time elapsed: 0.002 s
% 1.57/0.59  % (21267)------------------------------
% 1.57/0.59  % (21267)------------------------------
% 1.57/0.59  % (21252)Refutation not found, incomplete strategy% (21252)------------------------------
% 1.57/0.59  % (21252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (21252)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (21252)Memory used [KB]: 1791
% 1.57/0.59  % (21252)Time elapsed: 0.164 s
% 1.57/0.59  % (21252)------------------------------
% 1.57/0.59  % (21252)------------------------------
% 1.57/0.59  % (21278)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.57/0.59  % (21271)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.57/0.60  % (21268)Refutation found. Thanks to Tanya!
% 1.57/0.60  % SZS status Theorem for theBenchmark
% 1.57/0.60  % SZS output start Proof for theBenchmark
% 1.57/0.60  fof(f938,plain,(
% 1.57/0.60    $false),
% 1.57/0.60    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f63,f77,f293,f312,f317,f383,f453,f498,f549,f616,f929,f937])).
% 1.57/0.60  fof(f937,plain,(
% 1.57/0.60    spl5_1 | ~spl5_53 | ~spl5_68),
% 1.57/0.60    inference(avatar_split_clause,[],[f936,f912,f610,f39])).
% 1.57/0.60  fof(f39,plain,(
% 1.57/0.60    spl5_1 <=> sK0 = sK2),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.57/0.60  fof(f610,plain,(
% 1.57/0.60    spl5_53 <=> sK0 = k2_xboole_0(sK0,sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 1.57/0.60  fof(f912,plain,(
% 1.57/0.60    spl5_68 <=> r1_tarski(sK0,sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 1.57/0.60  fof(f936,plain,(
% 1.57/0.60    sK0 = sK2 | (~spl5_53 | ~spl5_68)),
% 1.57/0.60    inference(forward_demodulation,[],[f935,f612])).
% 1.57/0.60  fof(f612,plain,(
% 1.57/0.60    sK0 = k2_xboole_0(sK0,sK2) | ~spl5_53),
% 1.57/0.60    inference(avatar_component_clause,[],[f610])).
% 1.57/0.60  fof(f935,plain,(
% 1.57/0.60    sK2 = k2_xboole_0(sK0,sK2) | ~spl5_68),
% 1.57/0.60    inference(resolution,[],[f914,f33])).
% 1.57/0.60  fof(f33,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.57/0.60    inference(cnf_transformation,[],[f18])).
% 1.57/0.60  fof(f18,plain,(
% 1.57/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.57/0.60    inference(ennf_transformation,[],[f4])).
% 1.57/0.60  fof(f4,axiom,(
% 1.57/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.57/0.60  fof(f914,plain,(
% 1.57/0.60    r1_tarski(sK0,sK2) | ~spl5_68),
% 1.57/0.60    inference(avatar_component_clause,[],[f912])).
% 1.57/0.60  fof(f929,plain,(
% 1.57/0.60    spl5_68 | ~spl5_6 | ~spl5_44),
% 1.57/0.60    inference(avatar_split_clause,[],[f928,f546,f71,f912])).
% 1.57/0.60  fof(f71,plain,(
% 1.57/0.60    spl5_6 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.57/0.60  fof(f546,plain,(
% 1.57/0.60    spl5_44 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 1.57/0.60  fof(f928,plain,(
% 1.57/0.60    r1_tarski(sK0,sK2) | (~spl5_6 | ~spl5_44)),
% 1.57/0.60    inference(forward_demodulation,[],[f927,f548])).
% 1.57/0.60  fof(f548,plain,(
% 1.57/0.60    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_44),
% 1.57/0.60    inference(avatar_component_clause,[],[f546])).
% 1.57/0.60  fof(f927,plain,(
% 1.57/0.60    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | (~spl5_6 | ~spl5_44)),
% 1.57/0.60    inference(forward_demodulation,[],[f905,f548])).
% 1.57/0.60  fof(f905,plain,(
% 1.57/0.60    r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),sK2) | ~spl5_6),
% 1.57/0.60    inference(resolution,[],[f125,f96])).
% 1.57/0.60  fof(f96,plain,(
% 1.57/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,X0),k2_xboole_0(X1,X0))) )),
% 1.57/0.60    inference(superposition,[],[f91,f27])).
% 1.57/0.60  fof(f27,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f1])).
% 1.57/0.60  fof(f1,axiom,(
% 1.57/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.57/0.60  fof(f91,plain,(
% 1.57/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 1.57/0.60    inference(superposition,[],[f66,f30])).
% 1.57/0.60  fof(f30,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f5])).
% 1.57/0.60  fof(f5,axiom,(
% 1.57/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.57/0.60  fof(f66,plain,(
% 1.57/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.57/0.60    inference(superposition,[],[f26,f27])).
% 1.57/0.60  fof(f26,plain,(
% 1.57/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f10])).
% 1.57/0.60  fof(f10,axiom,(
% 1.57/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.57/0.60  fof(f125,plain,(
% 1.57/0.60    ( ! [X10] : (~r1_tarski(X10,k2_xboole_0(sK0,sK1)) | r1_tarski(k4_xboole_0(X10,sK1),sK2)) ) | ~spl5_6),
% 1.57/0.60    inference(superposition,[],[f34,f73])).
% 1.57/0.60  fof(f73,plain,(
% 1.57/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) | ~spl5_6),
% 1.57/0.60    inference(avatar_component_clause,[],[f71])).
% 1.57/0.60  fof(f34,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f19])).
% 1.57/0.60  fof(f19,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.57/0.60    inference(ennf_transformation,[],[f7])).
% 1.57/0.60  fof(f7,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.57/0.60  fof(f616,plain,(
% 1.57/0.60    spl5_53 | ~spl5_42),
% 1.57/0.60    inference(avatar_split_clause,[],[f602,f495,f610])).
% 1.57/0.60  fof(f495,plain,(
% 1.57/0.60    spl5_42 <=> sK0 = k2_xboole_0(sK2,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.57/0.60  fof(f602,plain,(
% 1.57/0.60    sK0 = k2_xboole_0(sK0,sK2) | ~spl5_42),
% 1.57/0.60    inference(superposition,[],[f27,f497])).
% 1.57/0.60  fof(f497,plain,(
% 1.57/0.60    sK0 = k2_xboole_0(sK2,sK0) | ~spl5_42),
% 1.57/0.60    inference(avatar_component_clause,[],[f495])).
% 1.57/0.60  fof(f549,plain,(
% 1.57/0.60    spl5_44 | ~spl5_26),
% 1.57/0.60    inference(avatar_split_clause,[],[f544,f314,f546])).
% 1.57/0.60  fof(f314,plain,(
% 1.57/0.60    spl5_26 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.57/0.60  fof(f544,plain,(
% 1.57/0.60    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_26),
% 1.57/0.60    inference(forward_demodulation,[],[f526,f24])).
% 1.57/0.60  fof(f24,plain,(
% 1.57/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(cnf_transformation,[],[f6])).
% 1.57/0.60  fof(f6,axiom,(
% 1.57/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.57/0.60  fof(f526,plain,(
% 1.57/0.60    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl5_26),
% 1.57/0.60    inference(superposition,[],[f35,f316])).
% 1.57/0.60  fof(f316,plain,(
% 1.57/0.60    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_26),
% 1.57/0.60    inference(avatar_component_clause,[],[f314])).
% 1.57/0.60  fof(f35,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.57/0.60    inference(definition_unfolding,[],[f29,f28])).
% 1.57/0.60  fof(f28,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f9])).
% 1.57/0.60  fof(f9,axiom,(
% 1.57/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.57/0.60  fof(f29,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f8])).
% 1.57/0.60  fof(f8,axiom,(
% 1.57/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.57/0.60  fof(f498,plain,(
% 1.57/0.60    spl5_42 | ~spl5_38),
% 1.57/0.60    inference(avatar_split_clause,[],[f493,f450,f495])).
% 1.57/0.60  fof(f450,plain,(
% 1.57/0.60    spl5_38 <=> r1_tarski(sK2,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.57/0.60  fof(f493,plain,(
% 1.57/0.60    sK0 = k2_xboole_0(sK2,sK0) | ~spl5_38),
% 1.57/0.60    inference(resolution,[],[f452,f33])).
% 1.57/0.60  fof(f452,plain,(
% 1.57/0.60    r1_tarski(sK2,sK0) | ~spl5_38),
% 1.57/0.60    inference(avatar_component_clause,[],[f450])).
% 1.57/0.60  fof(f453,plain,(
% 1.57/0.60    spl5_38 | ~spl5_22 | ~spl5_30),
% 1.57/0.60    inference(avatar_split_clause,[],[f440,f380,f290,f450])).
% 1.57/0.60  fof(f290,plain,(
% 1.57/0.60    spl5_22 <=> r1_tarski(k4_xboole_0(sK2,sK1),sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.57/0.60  fof(f380,plain,(
% 1.57/0.60    spl5_30 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.57/0.60  fof(f440,plain,(
% 1.57/0.60    r1_tarski(sK2,sK0) | (~spl5_22 | ~spl5_30)),
% 1.57/0.60    inference(backward_demodulation,[],[f292,f382])).
% 1.57/0.60  fof(f382,plain,(
% 1.57/0.60    sK2 = k4_xboole_0(sK2,sK1) | ~spl5_30),
% 1.57/0.60    inference(avatar_component_clause,[],[f380])).
% 1.57/0.60  fof(f292,plain,(
% 1.57/0.60    r1_tarski(k4_xboole_0(sK2,sK1),sK0) | ~spl5_22),
% 1.57/0.60    inference(avatar_component_clause,[],[f290])).
% 1.57/0.60  fof(f383,plain,(
% 1.57/0.60    spl5_30 | ~spl5_25),
% 1.57/0.60    inference(avatar_split_clause,[],[f378,f309,f380])).
% 1.57/0.60  fof(f309,plain,(
% 1.57/0.60    spl5_25 <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.57/0.60  fof(f378,plain,(
% 1.57/0.60    sK2 = k4_xboole_0(sK2,sK1) | ~spl5_25),
% 1.57/0.60    inference(forward_demodulation,[],[f369,f24])).
% 1.57/0.60  fof(f369,plain,(
% 1.57/0.60    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k1_xboole_0) | ~spl5_25),
% 1.57/0.60    inference(superposition,[],[f35,f311])).
% 1.57/0.60  fof(f311,plain,(
% 1.57/0.60    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | ~spl5_25),
% 1.57/0.60    inference(avatar_component_clause,[],[f309])).
% 1.57/0.60  fof(f317,plain,(
% 1.57/0.60    spl5_26 | ~spl5_3),
% 1.57/0.60    inference(avatar_split_clause,[],[f307,f49,f314])).
% 1.57/0.60  fof(f49,plain,(
% 1.57/0.60    spl5_3 <=> r1_xboole_0(sK0,sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.57/0.60  fof(f307,plain,(
% 1.57/0.60    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_3),
% 1.57/0.60    inference(resolution,[],[f139,f51])).
% 1.57/0.60  fof(f51,plain,(
% 1.57/0.60    r1_xboole_0(sK0,sK1) | ~spl5_3),
% 1.57/0.60    inference(avatar_component_clause,[],[f49])).
% 1.57/0.60  fof(f139,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.57/0.60    inference(resolution,[],[f37,f25])).
% 1.57/0.60  fof(f25,plain,(
% 1.57/0.60    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.57/0.60    inference(cnf_transformation,[],[f16])).
% 1.57/0.60  fof(f16,plain,(
% 1.57/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.57/0.60    inference(ennf_transformation,[],[f3])).
% 1.57/0.60  fof(f3,axiom,(
% 1.57/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.57/0.60  fof(f37,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.57/0.60    inference(definition_unfolding,[],[f31,f28])).
% 1.57/0.60  fof(f31,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f17])).
% 1.57/0.60  fof(f17,plain,(
% 1.57/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.60    inference(ennf_transformation,[],[f13])).
% 1.57/0.60  fof(f13,plain,(
% 1.57/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.60    inference(rectify,[],[f2])).
% 1.57/0.60  fof(f2,axiom,(
% 1.57/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.57/0.60  fof(f312,plain,(
% 1.57/0.60    spl5_25 | ~spl5_2),
% 1.57/0.60    inference(avatar_split_clause,[],[f306,f44,f309])).
% 1.57/0.60  fof(f44,plain,(
% 1.57/0.60    spl5_2 <=> r1_xboole_0(sK2,sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.57/0.60  fof(f306,plain,(
% 1.57/0.60    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | ~spl5_2),
% 1.57/0.60    inference(resolution,[],[f139,f46])).
% 1.57/0.60  fof(f46,plain,(
% 1.57/0.60    r1_xboole_0(sK2,sK1) | ~spl5_2),
% 1.57/0.60    inference(avatar_component_clause,[],[f44])).
% 1.57/0.60  fof(f293,plain,(
% 1.57/0.60    spl5_22 | ~spl5_5),
% 1.57/0.60    inference(avatar_split_clause,[],[f272,f60,f290])).
% 1.57/0.60  fof(f60,plain,(
% 1.57/0.60    spl5_5 <=> r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.57/0.60  fof(f272,plain,(
% 1.57/0.60    r1_tarski(k4_xboole_0(sK2,sK1),sK0) | ~spl5_5),
% 1.57/0.60    inference(resolution,[],[f122,f62])).
% 1.57/0.60  fof(f62,plain,(
% 1.57/0.60    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | ~spl5_5),
% 1.57/0.60    inference(avatar_component_clause,[],[f60])).
% 1.57/0.60  fof(f122,plain,(
% 1.57/0.60    ( ! [X2,X3,X1] : (~r1_tarski(X3,k2_xboole_0(X2,X1)) | r1_tarski(k4_xboole_0(X3,X1),X2)) )),
% 1.57/0.60    inference(superposition,[],[f34,f27])).
% 1.57/0.60  fof(f77,plain,(
% 1.57/0.60    spl5_6 | ~spl5_4),
% 1.57/0.60    inference(avatar_split_clause,[],[f69,f54,f71])).
% 1.57/0.60  fof(f54,plain,(
% 1.57/0.60    spl5_4 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.57/0.60  fof(f69,plain,(
% 1.57/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) | ~spl5_4),
% 1.57/0.60    inference(superposition,[],[f56,f27])).
% 1.57/0.60  fof(f56,plain,(
% 1.57/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) | ~spl5_4),
% 1.57/0.60    inference(avatar_component_clause,[],[f54])).
% 1.57/0.60  fof(f63,plain,(
% 1.57/0.60    spl5_5 | ~spl5_4),
% 1.57/0.60    inference(avatar_split_clause,[],[f58,f54,f60])).
% 1.57/0.60  fof(f58,plain,(
% 1.57/0.60    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | ~spl5_4),
% 1.57/0.60    inference(superposition,[],[f26,f56])).
% 1.57/0.60  fof(f57,plain,(
% 1.57/0.60    spl5_4),
% 1.57/0.60    inference(avatar_split_clause,[],[f20,f54])).
% 1.57/0.60  fof(f20,plain,(
% 1.57/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 1.57/0.60    inference(cnf_transformation,[],[f15])).
% 1.57/0.60  fof(f15,plain,(
% 1.57/0.60    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 1.57/0.60    inference(flattening,[],[f14])).
% 1.57/0.60  fof(f14,plain,(
% 1.57/0.60    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 1.57/0.60    inference(ennf_transformation,[],[f12])).
% 1.57/0.60  fof(f12,negated_conjecture,(
% 1.57/0.60    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.57/0.60    inference(negated_conjecture,[],[f11])).
% 1.57/0.60  fof(f11,conjecture,(
% 1.57/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 1.57/0.60  fof(f52,plain,(
% 1.57/0.60    spl5_3),
% 1.57/0.60    inference(avatar_split_clause,[],[f21,f49])).
% 1.57/0.60  fof(f21,plain,(
% 1.57/0.60    r1_xboole_0(sK0,sK1)),
% 1.57/0.60    inference(cnf_transformation,[],[f15])).
% 1.57/0.60  fof(f47,plain,(
% 1.57/0.60    spl5_2),
% 1.57/0.60    inference(avatar_split_clause,[],[f22,f44])).
% 1.57/0.60  fof(f22,plain,(
% 1.57/0.60    r1_xboole_0(sK2,sK1)),
% 1.57/0.60    inference(cnf_transformation,[],[f15])).
% 1.57/0.60  fof(f42,plain,(
% 1.57/0.60    ~spl5_1),
% 1.57/0.60    inference(avatar_split_clause,[],[f23,f39])).
% 1.57/0.60  fof(f23,plain,(
% 1.57/0.60    sK0 != sK2),
% 1.57/0.60    inference(cnf_transformation,[],[f15])).
% 1.57/0.60  % SZS output end Proof for theBenchmark
% 1.57/0.60  % (21268)------------------------------
% 1.57/0.60  % (21268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.60  % (21268)Termination reason: Refutation
% 1.57/0.60  
% 1.57/0.60  % (21268)Memory used [KB]: 11257
% 1.57/0.60  % (21268)Time elapsed: 0.164 s
% 1.57/0.60  % (21268)------------------------------
% 1.57/0.60  % (21268)------------------------------
% 1.57/0.60  % (21281)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.60  % (21280)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.57/0.60  % (21261)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.57/0.61  % (21270)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.61  % (21251)Success in time 0.243 s
%------------------------------------------------------------------------------
