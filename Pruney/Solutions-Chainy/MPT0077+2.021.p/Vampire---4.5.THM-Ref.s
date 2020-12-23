%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:46 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 205 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 ( 494 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f973,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f75,f143,f145,f157,f166,f183,f189,f254,f869,f874,f952])).

fof(f952,plain,
    ( ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f951])).

fof(f951,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f950,f82])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f81,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f47,f36])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f81,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f76,f36])).

fof(f76,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f34,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f950,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f943,f873])).

fof(f873,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f871])).

fof(f871,plain,
    ( spl5_13
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f943,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f253,f940])).

fof(f940,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f924,f86])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f45,f36])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f924,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0))
    | ~ spl5_12 ),
    inference(superposition,[],[f115,f868])).

fof(f868,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f866])).

fof(f866,plain,
    ( spl5_12
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f115,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X5)) = k4_xboole_0(X3,k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f106,f45])).

fof(f106,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X5)) = k4_xboole_0(k4_xboole_0(X3,X4),X5) ),
    inference(superposition,[],[f45,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f253,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl5_9
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f874,plain,
    ( spl5_13
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f212,f154,f871])).

fof(f154,plain,
    ( spl5_5
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f212,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f191,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f191,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f155,f49])).

fof(f155,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f869,plain,
    ( spl5_12
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f207,f53,f866])).

fof(f53,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f207,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f147,f37])).

fof(f147,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f55,f49])).

fof(f55,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f254,plain,
    ( spl5_9
    | spl5_2 ),
    inference(avatar_split_clause,[],[f194,f57,f251])).

fof(f57,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f194,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f189,plain,
    ( spl5_2
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f171,f187])).

fof(f187,plain,
    ( r1_xboole_0(sK0,sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f33,f58])).

fof(f33,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f171,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f165,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f165,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl5_6
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f183,plain,
    ( ~ spl5_4
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl5_4
    | spl5_6 ),
    inference(subsumption_resolution,[],[f178,f66])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f178,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl5_4
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f165,f142,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f142,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_4
  <=> r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f166,plain,
    ( ~ spl5_6
    | spl5_5 ),
    inference(avatar_split_clause,[],[f161,f154,f163])).

fof(f161,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f156,f44])).

fof(f156,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f157,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f146,f57,f154,f53])).

fof(f146,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f28,f59])).

fof(f59,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f145,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f142,f130])).

fof(f130,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(sK1,X0),sK0)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f38,f74,f46])).

fof(f74,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_3
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f143,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f63,f57,f140])).

fof(f63,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f59,f44])).

fof(f75,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f61,f53,f72])).

fof(f61,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f54,f44])).

fof(f54,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f60,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f32,f57,f53])).

fof(f32,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:54:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (10310)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (10308)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (10303)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (10307)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (10306)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (10316)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (10304)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (10315)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (10302)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (10311)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (10312)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (10317)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (10305)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (10314)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.53  % (10309)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.55  % (10313)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.55  % (10313)Refutation not found, incomplete strategy% (10313)------------------------------
% 0.21/0.55  % (10313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10313)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10313)Memory used [KB]: 10618
% 0.21/0.55  % (10313)Time elapsed: 0.121 s
% 0.21/0.55  % (10313)------------------------------
% 0.21/0.55  % (10313)------------------------------
% 1.52/0.56  % (10318)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.52/0.56  % (10319)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.68/0.60  % (10317)Refutation found. Thanks to Tanya!
% 1.68/0.60  % SZS status Theorem for theBenchmark
% 1.68/0.60  % SZS output start Proof for theBenchmark
% 1.68/0.60  fof(f973,plain,(
% 1.68/0.60    $false),
% 1.68/0.60    inference(avatar_sat_refutation,[],[f60,f75,f143,f145,f157,f166,f183,f189,f254,f869,f874,f952])).
% 1.68/0.60  fof(f952,plain,(
% 1.68/0.60    ~spl5_9 | ~spl5_12 | ~spl5_13),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f951])).
% 1.68/0.60  fof(f951,plain,(
% 1.68/0.60    $false | (~spl5_9 | ~spl5_12 | ~spl5_13)),
% 1.68/0.60    inference(subsumption_resolution,[],[f950,f82])).
% 1.68/0.60  fof(f82,plain,(
% 1.68/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.68/0.60    inference(forward_demodulation,[],[f81,f51])).
% 1.68/0.60  fof(f51,plain,(
% 1.68/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.68/0.60    inference(backward_demodulation,[],[f47,f36])).
% 1.68/0.60  fof(f36,plain,(
% 1.68/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.68/0.60    inference(cnf_transformation,[],[f6])).
% 1.68/0.60  fof(f6,axiom,(
% 1.68/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.68/0.60  fof(f47,plain,(
% 1.68/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.68/0.60    inference(definition_unfolding,[],[f35,f40])).
% 1.68/0.60  fof(f40,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f9])).
% 1.68/0.60  fof(f9,axiom,(
% 1.68/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.68/0.60  fof(f35,plain,(
% 1.68/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f5])).
% 1.68/0.60  fof(f5,axiom,(
% 1.68/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.68/0.60  fof(f81,plain,(
% 1.68/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 1.68/0.60    inference(forward_demodulation,[],[f76,f36])).
% 1.68/0.60  fof(f76,plain,(
% 1.68/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) )),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f34,f49])).
% 1.68/0.60  fof(f49,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.68/0.60    inference(definition_unfolding,[],[f43,f40])).
% 1.68/0.60  fof(f43,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f27])).
% 1.68/0.60  fof(f27,plain,(
% 1.68/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.68/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f26])).
% 1.68/0.60  fof(f26,plain,(
% 1.68/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.68/0.60    introduced(choice_axiom,[])).
% 1.68/0.60  fof(f18,plain,(
% 1.68/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.68/0.60    inference(ennf_transformation,[],[f15])).
% 1.68/0.60  fof(f15,plain,(
% 1.68/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.68/0.60    inference(rectify,[],[f3])).
% 1.68/0.60  fof(f3,axiom,(
% 1.68/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.68/0.60  fof(f34,plain,(
% 1.68/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f11])).
% 1.68/0.60  fof(f11,axiom,(
% 1.68/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.68/0.60  fof(f950,plain,(
% 1.68/0.60    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) | (~spl5_9 | ~spl5_12 | ~spl5_13)),
% 1.68/0.60    inference(forward_demodulation,[],[f943,f873])).
% 1.68/0.60  fof(f873,plain,(
% 1.68/0.60    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_13),
% 1.68/0.60    inference(avatar_component_clause,[],[f871])).
% 1.68/0.60  fof(f871,plain,(
% 1.68/0.60    spl5_13 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.68/0.60  fof(f943,plain,(
% 1.68/0.60    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (~spl5_9 | ~spl5_12)),
% 1.68/0.60    inference(backward_demodulation,[],[f253,f940])).
% 1.68/0.60  fof(f940,plain,(
% 1.68/0.60    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl5_12),
% 1.68/0.60    inference(forward_demodulation,[],[f924,f86])).
% 1.68/0.60  fof(f86,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 1.68/0.60    inference(superposition,[],[f45,f36])).
% 1.68/0.60  fof(f45,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f7])).
% 1.68/0.60  fof(f7,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.68/0.60  fof(f924,plain,(
% 1.68/0.60    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0))) ) | ~spl5_12),
% 1.68/0.60    inference(superposition,[],[f115,f868])).
% 1.68/0.60  fof(f868,plain,(
% 1.68/0.60    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_12),
% 1.68/0.60    inference(avatar_component_clause,[],[f866])).
% 1.68/0.60  fof(f866,plain,(
% 1.68/0.60    spl5_12 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.68/0.60  fof(f115,plain,(
% 1.68/0.60    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X5)) = k4_xboole_0(X3,k2_xboole_0(X4,X5))) )),
% 1.68/0.60    inference(forward_demodulation,[],[f106,f45])).
% 1.68/0.60  fof(f106,plain,(
% 1.68/0.60    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X5)) = k4_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 1.68/0.60    inference(superposition,[],[f45,f48])).
% 1.68/0.60  fof(f48,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.68/0.60    inference(definition_unfolding,[],[f41,f40])).
% 1.68/0.60  fof(f41,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f8])).
% 1.68/0.60  fof(f8,axiom,(
% 1.68/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.68/0.60  fof(f253,plain,(
% 1.68/0.60    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))) | ~spl5_9),
% 1.68/0.60    inference(avatar_component_clause,[],[f251])).
% 1.68/0.60  fof(f251,plain,(
% 1.68/0.60    spl5_9 <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.68/0.60  fof(f874,plain,(
% 1.68/0.60    spl5_13 | ~spl5_5),
% 1.68/0.60    inference(avatar_split_clause,[],[f212,f154,f871])).
% 1.68/0.60  fof(f154,plain,(
% 1.68/0.60    spl5_5 <=> r1_xboole_0(sK0,sK2)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.68/0.60  fof(f212,plain,(
% 1.68/0.60    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_5),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f191,f37])).
% 1.68/0.60  fof(f37,plain,(
% 1.68/0.60    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.68/0.60    inference(cnf_transformation,[],[f25])).
% 1.68/0.60  fof(f25,plain,(
% 1.68/0.60    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.68/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f24])).
% 1.68/0.60  fof(f24,plain,(
% 1.68/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.68/0.60    introduced(choice_axiom,[])).
% 1.68/0.60  fof(f17,plain,(
% 1.68/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.68/0.60    inference(ennf_transformation,[],[f4])).
% 1.68/0.60  fof(f4,axiom,(
% 1.68/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.68/0.60  fof(f191,plain,(
% 1.68/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ) | ~spl5_5),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f155,f49])).
% 1.68/0.60  fof(f155,plain,(
% 1.68/0.60    r1_xboole_0(sK0,sK2) | ~spl5_5),
% 1.68/0.60    inference(avatar_component_clause,[],[f154])).
% 1.68/0.60  fof(f869,plain,(
% 1.68/0.60    spl5_12 | ~spl5_1),
% 1.68/0.60    inference(avatar_split_clause,[],[f207,f53,f866])).
% 1.68/0.60  fof(f53,plain,(
% 1.68/0.60    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.68/0.60  fof(f207,plain,(
% 1.68/0.60    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_1),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f147,f37])).
% 1.68/0.60  fof(f147,plain,(
% 1.68/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl5_1),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f55,f49])).
% 1.68/0.60  fof(f55,plain,(
% 1.68/0.60    r1_xboole_0(sK0,sK1) | ~spl5_1),
% 1.68/0.60    inference(avatar_component_clause,[],[f53])).
% 1.68/0.60  fof(f254,plain,(
% 1.68/0.60    spl5_9 | spl5_2),
% 1.68/0.60    inference(avatar_split_clause,[],[f194,f57,f251])).
% 1.68/0.60  fof(f57,plain,(
% 1.68/0.60    spl5_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.68/0.60  fof(f194,plain,(
% 1.68/0.60    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))) | spl5_2),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f58,f50])).
% 1.68/0.60  fof(f50,plain,(
% 1.68/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.68/0.60    inference(definition_unfolding,[],[f42,f40])).
% 1.68/0.60  fof(f42,plain,(
% 1.68/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f27])).
% 1.68/0.60  fof(f58,plain,(
% 1.68/0.60    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl5_2),
% 1.68/0.60    inference(avatar_component_clause,[],[f57])).
% 1.68/0.60  fof(f189,plain,(
% 1.68/0.60    spl5_2 | spl5_6),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f188])).
% 1.68/0.60  fof(f188,plain,(
% 1.68/0.60    $false | (spl5_2 | spl5_6)),
% 1.68/0.60    inference(subsumption_resolution,[],[f171,f187])).
% 1.68/0.60  fof(f187,plain,(
% 1.68/0.60    r1_xboole_0(sK0,sK2) | spl5_2),
% 1.68/0.60    inference(subsumption_resolution,[],[f33,f58])).
% 1.68/0.60  fof(f33,plain,(
% 1.68/0.60    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 1.68/0.60    inference(cnf_transformation,[],[f23])).
% 1.68/0.60  fof(f23,plain,(
% 1.68/0.60    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.68/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f22])).
% 1.68/0.60  fof(f22,plain,(
% 1.68/0.60    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 1.68/0.60    introduced(choice_axiom,[])).
% 1.68/0.60  fof(f16,plain,(
% 1.68/0.60    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.68/0.60    inference(ennf_transformation,[],[f14])).
% 1.68/0.60  fof(f14,negated_conjecture,(
% 1.68/0.60    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.68/0.60    inference(negated_conjecture,[],[f13])).
% 1.68/0.60  fof(f13,conjecture,(
% 1.68/0.60    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.68/0.60  fof(f171,plain,(
% 1.68/0.60    ~r1_xboole_0(sK0,sK2) | spl5_6),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f165,f44])).
% 1.68/0.60  fof(f44,plain,(
% 1.68/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f19])).
% 1.68/0.60  fof(f19,plain,(
% 1.68/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.68/0.60    inference(ennf_transformation,[],[f2])).
% 1.68/0.60  fof(f2,axiom,(
% 1.68/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.68/0.60  fof(f165,plain,(
% 1.68/0.60    ~r1_xboole_0(sK2,sK0) | spl5_6),
% 1.68/0.60    inference(avatar_component_clause,[],[f163])).
% 1.68/0.60  fof(f163,plain,(
% 1.68/0.60    spl5_6 <=> r1_xboole_0(sK2,sK0)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.68/0.60  fof(f183,plain,(
% 1.68/0.60    ~spl5_4 | spl5_6),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f182])).
% 1.68/0.60  fof(f182,plain,(
% 1.68/0.60    $false | (~spl5_4 | spl5_6)),
% 1.68/0.60    inference(subsumption_resolution,[],[f178,f66])).
% 1.68/0.60  fof(f66,plain,(
% 1.68/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.68/0.60    inference(superposition,[],[f38,f39])).
% 1.68/0.60  fof(f39,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f1])).
% 1.68/0.60  fof(f1,axiom,(
% 1.68/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.68/0.60  fof(f38,plain,(
% 1.68/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.68/0.60    inference(cnf_transformation,[],[f12])).
% 1.68/0.60  fof(f12,axiom,(
% 1.68/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.68/0.60  fof(f178,plain,(
% 1.68/0.60    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (~spl5_4 | spl5_6)),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f165,f142,f46])).
% 1.68/0.60  fof(f46,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f21])).
% 1.68/0.60  fof(f21,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.68/0.60    inference(flattening,[],[f20])).
% 1.68/0.60  fof(f20,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.68/0.60    inference(ennf_transformation,[],[f10])).
% 1.68/0.60  fof(f10,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.68/0.60  fof(f142,plain,(
% 1.68/0.60    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl5_4),
% 1.68/0.60    inference(avatar_component_clause,[],[f140])).
% 1.68/0.60  fof(f140,plain,(
% 1.68/0.60    spl5_4 <=> r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.68/0.60  fof(f166,plain,(
% 1.68/0.60    ~spl5_6 | spl5_5),
% 1.68/0.60    inference(avatar_split_clause,[],[f161,f154,f163])).
% 1.68/0.60  fof(f161,plain,(
% 1.68/0.60    ~r1_xboole_0(sK2,sK0) | spl5_5),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f156,f44])).
% 1.68/0.60  fof(f156,plain,(
% 1.68/0.60    ~r1_xboole_0(sK0,sK2) | spl5_5),
% 1.68/0.60    inference(avatar_component_clause,[],[f154])).
% 1.68/0.60  fof(f157,plain,(
% 1.68/0.60    ~spl5_1 | ~spl5_5 | ~spl5_2),
% 1.68/0.60    inference(avatar_split_clause,[],[f146,f57,f154,f53])).
% 1.68/0.60  fof(f146,plain,(
% 1.68/0.60    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~spl5_2),
% 1.68/0.60    inference(subsumption_resolution,[],[f28,f59])).
% 1.68/0.60  fof(f59,plain,(
% 1.68/0.60    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_2),
% 1.68/0.60    inference(avatar_component_clause,[],[f57])).
% 1.68/0.60  fof(f28,plain,(
% 1.68/0.60    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.68/0.60    inference(cnf_transformation,[],[f23])).
% 1.68/0.60  fof(f145,plain,(
% 1.68/0.60    spl5_3 | ~spl5_4),
% 1.68/0.60    inference(avatar_contradiction_clause,[],[f144])).
% 1.68/0.60  fof(f144,plain,(
% 1.68/0.60    $false | (spl5_3 | ~spl5_4)),
% 1.68/0.60    inference(subsumption_resolution,[],[f142,f130])).
% 1.68/0.60  fof(f130,plain,(
% 1.68/0.60    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(sK1,X0),sK0)) ) | spl5_3),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f38,f74,f46])).
% 1.68/0.60  fof(f74,plain,(
% 1.68/0.60    ~r1_xboole_0(sK1,sK0) | spl5_3),
% 1.68/0.60    inference(avatar_component_clause,[],[f72])).
% 1.68/0.60  fof(f72,plain,(
% 1.68/0.60    spl5_3 <=> r1_xboole_0(sK1,sK0)),
% 1.68/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.68/0.60  fof(f143,plain,(
% 1.68/0.60    spl5_4 | ~spl5_2),
% 1.68/0.60    inference(avatar_split_clause,[],[f63,f57,f140])).
% 1.68/0.60  fof(f63,plain,(
% 1.68/0.60    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl5_2),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f59,f44])).
% 1.68/0.60  fof(f75,plain,(
% 1.68/0.60    ~spl5_3 | spl5_1),
% 1.68/0.60    inference(avatar_split_clause,[],[f61,f53,f72])).
% 1.68/0.60  fof(f61,plain,(
% 1.68/0.60    ~r1_xboole_0(sK1,sK0) | spl5_1),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f54,f44])).
% 1.68/0.60  fof(f54,plain,(
% 1.68/0.60    ~r1_xboole_0(sK0,sK1) | spl5_1),
% 1.68/0.60    inference(avatar_component_clause,[],[f53])).
% 1.68/0.60  fof(f60,plain,(
% 1.68/0.60    spl5_1 | spl5_2),
% 1.68/0.60    inference(avatar_split_clause,[],[f32,f57,f53])).
% 1.68/0.60  fof(f32,plain,(
% 1.68/0.60    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 1.68/0.60    inference(cnf_transformation,[],[f23])).
% 1.68/0.60  % SZS output end Proof for theBenchmark
% 1.68/0.60  % (10317)------------------------------
% 1.68/0.60  % (10317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (10317)Termination reason: Refutation
% 1.68/0.60  
% 1.68/0.60  % (10317)Memory used [KB]: 11513
% 1.68/0.60  % (10317)Time elapsed: 0.109 s
% 1.68/0.60  % (10317)------------------------------
% 1.68/0.60  % (10317)------------------------------
% 1.68/0.62  % (10301)Success in time 0.264 s
%------------------------------------------------------------------------------
