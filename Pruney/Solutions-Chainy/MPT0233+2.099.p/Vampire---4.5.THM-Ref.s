%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:16 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 662 expanded)
%              Number of leaves         :   16 ( 194 expanded)
%              Depth                    :   18
%              Number of atoms          :  298 (1324 expanded)
%              Number of equality atoms :  156 ( 957 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f413,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f179,f256,f330,f412])).

fof(f412,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f410,f366])).

fof(f366,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f348,f361])).

fof(f361,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(superposition,[],[f96,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_1
  <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f96,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f348,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f347,f342])).

fof(f342,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f335,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f335,plain,
    ( k4_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f102,f109])).

fof(f102,plain,(
    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f62,f99])).

fof(f99,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3))) ),
    inference(resolution,[],[f63,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f63,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f27,f60,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f347,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK3)))
    | ~ spl5_1 ),
    inference(inner_rewriting,[],[f338])).

fof(f338,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK3)))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f105,f109])).

fof(f105,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK3))) ),
    inference(inner_rewriting,[],[f101])).

fof(f101,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3))) ),
    inference(superposition,[],[f71,f99])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f42,f61,f60])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f410,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f409,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f409,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0))
    | ~ spl5_1 ),
    inference(resolution,[],[f358,f70])).

fof(f358,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl5_1 ),
    inference(superposition,[],[f88,f109])).

fof(f88,plain,(
    ! [X2,X1] : r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) != X0
      | r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f32,f61,f60])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f330,plain,
    ( spl5_1
    | spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f323,f312])).

fof(f312,plain,
    ( sK0 != sK1
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(superposition,[],[f29,f285])).

fof(f285,plain,
    ( sK1 = sK3
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f284,f29])).

fof(f284,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | sK0 = sK3
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(resolution,[],[f272,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f272,plain,
    ( r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(superposition,[],[f96,f259])).

fof(f259,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f258,f120])).

fof(f120,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_4
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f258,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f257,f108])).

fof(f108,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f257,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f186,f112])).

fof(f112,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK2,sK2,sK2,sK2,sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_2
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f186,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(resolution,[],[f63,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k3_enumset1(X2,X2,X2,X2,X2) = X0
      | k3_enumset1(X1,X1,X1,X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f61,f61,f60,f60])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f29,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f323,plain,
    ( sK0 = sK1
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(resolution,[],[f296,f96])).

fof(f296,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK1 = X9 )
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(backward_demodulation,[],[f275,f285])).

fof(f275,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK3 = X9 )
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK3 = X9
        | sK3 = X9
        | sK3 = X9 )
    | spl5_1
    | spl5_2
    | spl5_4 ),
    inference(superposition,[],[f97,f259])).

fof(f256,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f249,f223])).

fof(f223,plain,
    ( sK0 != sK1
    | ~ spl5_4 ),
    inference(superposition,[],[f28,f211])).

fof(f211,plain,
    ( sK1 = sK2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f210,f28])).

fof(f210,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | sK0 = sK2
    | ~ spl5_4 ),
    inference(resolution,[],[f198,f97])).

fof(f198,plain,
    ( r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_4 ),
    inference(superposition,[],[f96,f121])).

fof(f121,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f28,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f249,plain,
    ( sK0 = sK1
    | ~ spl5_4 ),
    inference(resolution,[],[f222,f96])).

fof(f222,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK1 = X9 )
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f201,f211])).

fof(f201,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK2 = X9 )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK2 = X9
        | sK2 = X9
        | sK2 = X9 )
    | ~ spl5_4 ),
    inference(superposition,[],[f97,f121])).

fof(f179,plain,
    ( ~ spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f173,f146])).

fof(f146,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_2
    | spl5_4 ),
    inference(backward_demodulation,[],[f120,f144])).

fof(f144,plain,
    ( sK1 = sK2
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f143,f28])).

fof(f143,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | sK0 = sK2
    | ~ spl5_2 ),
    inference(resolution,[],[f138,f97])).

fof(f138,plain,
    ( r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f96,f113])).

fof(f113,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f173,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f145,f169])).

fof(f169,plain,
    ( sK1 = sK3
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f168,f29])).

fof(f168,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | sK0 = sK3
    | ~ spl5_2 ),
    inference(resolution,[],[f140,f97])).

fof(f140,plain,
    ( r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f92,f113])).

fof(f92,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f145,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK3)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f113,f144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:35:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (12998)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.56  % (13015)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.57  % (13022)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.25/0.57  % (13016)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.25/0.57  % (13022)Refutation not found, incomplete strategy% (13022)------------------------------
% 1.25/0.57  % (13022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.57  % (13022)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.57  
% 1.25/0.57  % (13022)Memory used [KB]: 1663
% 1.25/0.57  % (13022)Time elapsed: 0.002 s
% 1.25/0.57  % (13022)------------------------------
% 1.25/0.57  % (13022)------------------------------
% 1.25/0.57  % (13009)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.25/0.57  % (12999)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.25/0.57  % (13009)Refutation not found, incomplete strategy% (13009)------------------------------
% 1.25/0.57  % (13009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.57  % (13009)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.57  
% 1.25/0.57  % (13009)Memory used [KB]: 10618
% 1.25/0.57  % (13009)Time elapsed: 0.109 s
% 1.25/0.57  % (13009)------------------------------
% 1.25/0.57  % (13009)------------------------------
% 1.25/0.57  % (12996)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.58  % (13003)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.59/0.58  % (13007)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.59/0.58  % (13019)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.59/0.58  % (13008)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.59/0.58  % (12992)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.59/0.58  % (13011)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.59/0.58  % (12997)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.59/0.58  % (12994)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.59/0.58  % (13006)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.59/0.58  % (12995)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.59/0.59  % (13005)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.59/0.59  % (13004)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.59/0.59  % (13005)Refutation not found, incomplete strategy% (13005)------------------------------
% 1.59/0.59  % (13005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (13005)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (13005)Memory used [KB]: 10618
% 1.59/0.59  % (13005)Time elapsed: 0.158 s
% 1.59/0.59  % (13005)------------------------------
% 1.59/0.59  % (13005)------------------------------
% 1.59/0.59  % (13010)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.59/0.59  % (13021)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.59/0.59  % (13020)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.59/0.59  % (13014)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.59/0.60  % (13013)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.59/0.60  % (13012)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.59/0.61  % (13018)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.59/0.62  % (13020)Refutation found. Thanks to Tanya!
% 1.59/0.62  % SZS status Theorem for theBenchmark
% 1.59/0.62  % SZS output start Proof for theBenchmark
% 1.59/0.62  fof(f413,plain,(
% 1.59/0.62    $false),
% 1.59/0.62    inference(avatar_sat_refutation,[],[f179,f256,f330,f412])).
% 1.59/0.62  fof(f412,plain,(
% 1.59/0.62    ~spl5_1),
% 1.59/0.62    inference(avatar_contradiction_clause,[],[f411])).
% 1.59/0.62  fof(f411,plain,(
% 1.59/0.62    $false | ~spl5_1),
% 1.59/0.62    inference(subsumption_resolution,[],[f410,f366])).
% 1.59/0.62  fof(f366,plain,(
% 1.59/0.62    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl5_1),
% 1.59/0.62    inference(subsumption_resolution,[],[f348,f361])).
% 1.59/0.62  fof(f361,plain,(
% 1.59/0.62    r2_hidden(sK0,k1_xboole_0) | ~spl5_1),
% 1.59/0.62    inference(superposition,[],[f96,f109])).
% 1.59/0.62  fof(f109,plain,(
% 1.59/0.62    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | ~spl5_1),
% 1.59/0.62    inference(avatar_component_clause,[],[f107])).
% 1.59/0.62  fof(f107,plain,(
% 1.59/0.62    spl5_1 <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 1.59/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.59/0.62  fof(f96,plain,(
% 1.59/0.62    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 1.59/0.62    inference(equality_resolution,[],[f95])).
% 1.59/0.62  fof(f95,plain,(
% 1.59/0.62    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 1.59/0.62    inference(equality_resolution,[],[f80])).
% 1.59/0.62  fof(f80,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.59/0.62    inference(definition_unfolding,[],[f52,f59])).
% 1.59/0.62  fof(f59,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f55,f58])).
% 1.59/0.62  fof(f58,plain,(
% 1.59/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f13])).
% 1.59/0.62  fof(f13,axiom,(
% 1.59/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.59/0.62  fof(f55,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f12])).
% 1.59/0.62  fof(f12,axiom,(
% 1.59/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.62  fof(f52,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.59/0.62    inference(cnf_transformation,[],[f26])).
% 1.59/0.62  fof(f26,plain,(
% 1.59/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.59/0.62    inference(ennf_transformation,[],[f9])).
% 1.59/0.62  fof(f9,axiom,(
% 1.59/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.59/0.62  fof(f348,plain,(
% 1.59/0.62    ~r2_hidden(sK0,k1_xboole_0) | k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl5_1),
% 1.59/0.62    inference(forward_demodulation,[],[f347,f342])).
% 1.59/0.62  fof(f342,plain,(
% 1.59/0.62    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK3)) | ~spl5_1),
% 1.59/0.62    inference(forward_demodulation,[],[f335,f43])).
% 1.59/0.62  fof(f43,plain,(
% 1.59/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.59/0.62    inference(cnf_transformation,[],[f8])).
% 1.59/0.62  fof(f8,axiom,(
% 1.59/0.62    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.59/0.62  fof(f335,plain,(
% 1.59/0.62    k4_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_1),
% 1.59/0.62    inference(backward_demodulation,[],[f102,f109])).
% 1.59/0.62  fof(f102,plain,(
% 1.59/0.62    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 1.59/0.62    inference(superposition,[],[f62,f99])).
% 1.59/0.62  fof(f99,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)))),
% 1.59/0.62    inference(resolution,[],[f63,f70])).
% 1.59/0.62  fof(f70,plain,(
% 1.59/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.59/0.62    inference(definition_unfolding,[],[f36,f56])).
% 1.59/0.62  fof(f56,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.59/0.62    inference(cnf_transformation,[],[f7])).
% 1.59/0.62  fof(f7,axiom,(
% 1.59/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.59/0.62  fof(f36,plain,(
% 1.59/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.59/0.62    inference(cnf_transformation,[],[f25])).
% 1.59/0.62  fof(f25,plain,(
% 1.59/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.59/0.62    inference(ennf_transformation,[],[f5])).
% 1.59/0.62  fof(f5,axiom,(
% 1.59/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.59/0.62  fof(f63,plain,(
% 1.59/0.62    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3))),
% 1.59/0.62    inference(definition_unfolding,[],[f27,f60,f60])).
% 1.59/0.62  fof(f60,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f37,f59])).
% 1.59/0.62  fof(f37,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f11])).
% 1.59/0.62  fof(f11,axiom,(
% 1.59/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.62  fof(f27,plain,(
% 1.59/0.62    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.59/0.62    inference(cnf_transformation,[],[f22])).
% 1.59/0.62  fof(f22,plain,(
% 1.59/0.62    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.59/0.62    inference(ennf_transformation,[],[f20])).
% 1.59/0.62  fof(f20,negated_conjecture,(
% 1.59/0.62    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.59/0.62    inference(negated_conjecture,[],[f19])).
% 1.59/0.62  fof(f19,conjecture,(
% 1.59/0.62    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.59/0.62  fof(f62,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.59/0.62    inference(definition_unfolding,[],[f57,f56])).
% 1.59/0.62  fof(f57,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.59/0.62    inference(cnf_transformation,[],[f3])).
% 1.59/0.62  fof(f3,axiom,(
% 1.59/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.59/0.62  fof(f347,plain,(
% 1.59/0.62    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK3))) | ~spl5_1),
% 1.59/0.62    inference(inner_rewriting,[],[f338])).
% 1.59/0.62  fof(f338,plain,(
% 1.59/0.62    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK3))) | ~spl5_1),
% 1.59/0.62    inference(backward_demodulation,[],[f105,f109])).
% 1.59/0.62  fof(f105,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK3)))),
% 1.59/0.62    inference(inner_rewriting,[],[f101])).
% 1.59/0.62  fof(f101,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)))),
% 1.59/0.62    inference(superposition,[],[f71,f99])).
% 1.59/0.62  fof(f71,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) != k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f42,f61,f60])).
% 1.59/0.62  fof(f61,plain,(
% 1.59/0.62    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f38,f60])).
% 1.59/0.62  fof(f38,plain,(
% 1.59/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f10])).
% 1.59/0.62  fof(f10,axiom,(
% 1.59/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.62  fof(f42,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f17])).
% 1.59/0.62  fof(f17,axiom,(
% 1.59/0.62    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.59/0.62  fof(f410,plain,(
% 1.59/0.62    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl5_1),
% 1.59/0.62    inference(forward_demodulation,[],[f409,f75])).
% 1.59/0.62  fof(f75,plain,(
% 1.59/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.59/0.62    inference(definition_unfolding,[],[f44,f56])).
% 1.59/0.62  fof(f44,plain,(
% 1.59/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f6])).
% 1.59/0.62  fof(f6,axiom,(
% 1.59/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.59/0.62  fof(f409,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) | ~spl5_1),
% 1.59/0.62    inference(resolution,[],[f358,f70])).
% 1.59/0.62  fof(f358,plain,(
% 1.59/0.62    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) | ~spl5_1),
% 1.59/0.62    inference(superposition,[],[f88,f109])).
% 1.59/0.62  fof(f88,plain,(
% 1.59/0.62    ( ! [X2,X1] : (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))) )),
% 1.59/0.62    inference(equality_resolution,[],[f66])).
% 1.59/0.62  fof(f66,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) != X0 | r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))) )),
% 1.59/0.62    inference(definition_unfolding,[],[f32,f61,f60])).
% 1.59/0.62  fof(f32,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.59/0.62    inference(cnf_transformation,[],[f23])).
% 1.59/0.62  fof(f23,plain,(
% 1.59/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.59/0.62    inference(ennf_transformation,[],[f18])).
% 1.59/0.62  fof(f18,axiom,(
% 1.59/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.59/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.59/0.62  fof(f330,plain,(
% 1.59/0.62    spl5_1 | spl5_2 | spl5_4),
% 1.59/0.62    inference(avatar_contradiction_clause,[],[f329])).
% 1.59/0.62  fof(f329,plain,(
% 1.59/0.62    $false | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(subsumption_resolution,[],[f323,f312])).
% 1.59/0.62  fof(f312,plain,(
% 1.59/0.62    sK0 != sK1 | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(superposition,[],[f29,f285])).
% 1.59/0.62  fof(f285,plain,(
% 1.59/0.62    sK1 = sK3 | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(subsumption_resolution,[],[f284,f29])).
% 1.59/0.62  fof(f284,plain,(
% 1.59/0.62    sK0 = sK3 | sK1 = sK3 | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(duplicate_literal_removal,[],[f283])).
% 1.59/0.62  fof(f283,plain,(
% 1.59/0.62    sK0 = sK3 | sK1 = sK3 | sK0 = sK3 | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(resolution,[],[f272,f97])).
% 1.59/0.62  fof(f97,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.59/0.62    inference(equality_resolution,[],[f81])).
% 1.59/0.62  fof(f81,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.59/0.62    inference(definition_unfolding,[],[f51,f59])).
% 1.59/0.62  fof(f51,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.59/0.62    inference(cnf_transformation,[],[f26])).
% 1.59/0.62  fof(f272,plain,(
% 1.59/0.62    r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(superposition,[],[f96,f259])).
% 1.59/0.62  fof(f259,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(subsumption_resolution,[],[f258,f120])).
% 1.59/0.62  fof(f120,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK2,sK2,sK2,sK2,sK2) | spl5_4),
% 1.59/0.62    inference(avatar_component_clause,[],[f119])).
% 1.59/0.62  fof(f119,plain,(
% 1.59/0.62    spl5_4 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 1.59/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.59/0.62  fof(f258,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | (spl5_1 | spl5_2)),
% 1.59/0.62    inference(subsumption_resolution,[],[f257,f108])).
% 1.59/0.62  fof(f108,plain,(
% 1.59/0.62    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK1) | spl5_1),
% 1.59/0.62    inference(avatar_component_clause,[],[f107])).
% 1.59/0.62  fof(f257,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | spl5_2),
% 1.59/0.62    inference(subsumption_resolution,[],[f186,f112])).
% 1.59/0.62  fof(f112,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK2,sK2,sK2,sK2,sK3) | spl5_2),
% 1.59/0.62    inference(avatar_component_clause,[],[f111])).
% 1.59/0.62  fof(f111,plain,(
% 1.59/0.62    spl5_2 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)),
% 1.59/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.59/0.62  fof(f186,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 1.59/0.62    inference(resolution,[],[f63,f68])).
% 1.59/0.62  fof(f68,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k3_enumset1(X2,X2,X2,X2,X2) = X0 | k3_enumset1(X1,X1,X1,X1,X2) = X0 | k1_xboole_0 = X0) )),
% 1.59/0.62    inference(definition_unfolding,[],[f30,f61,f61,f60,f60])).
% 1.59/0.62  fof(f30,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.59/0.62    inference(cnf_transformation,[],[f23])).
% 1.59/0.62  fof(f29,plain,(
% 1.59/0.62    sK0 != sK3),
% 1.59/0.62    inference(cnf_transformation,[],[f22])).
% 1.59/0.62  fof(f323,plain,(
% 1.59/0.62    sK0 = sK1 | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(resolution,[],[f296,f96])).
% 1.59/0.62  fof(f296,plain,(
% 1.59/0.62    ( ! [X9] : (~r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK1 = X9) ) | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(backward_demodulation,[],[f275,f285])).
% 1.59/0.62  fof(f275,plain,(
% 1.59/0.62    ( ! [X9] : (~r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK3 = X9) ) | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(duplicate_literal_removal,[],[f271])).
% 1.59/0.62  fof(f271,plain,(
% 1.59/0.62    ( ! [X9] : (~r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK3 = X9 | sK3 = X9 | sK3 = X9) ) | (spl5_1 | spl5_2 | spl5_4)),
% 1.59/0.62    inference(superposition,[],[f97,f259])).
% 1.59/0.62  fof(f256,plain,(
% 1.59/0.62    ~spl5_4),
% 1.59/0.62    inference(avatar_contradiction_clause,[],[f255])).
% 1.59/0.62  fof(f255,plain,(
% 1.59/0.62    $false | ~spl5_4),
% 1.59/0.62    inference(subsumption_resolution,[],[f249,f223])).
% 1.59/0.62  fof(f223,plain,(
% 1.59/0.62    sK0 != sK1 | ~spl5_4),
% 1.59/0.62    inference(superposition,[],[f28,f211])).
% 1.59/0.62  fof(f211,plain,(
% 1.59/0.62    sK1 = sK2 | ~spl5_4),
% 1.59/0.62    inference(subsumption_resolution,[],[f210,f28])).
% 1.59/0.62  fof(f210,plain,(
% 1.59/0.62    sK0 = sK2 | sK1 = sK2 | ~spl5_4),
% 1.59/0.62    inference(duplicate_literal_removal,[],[f209])).
% 1.59/0.62  fof(f209,plain,(
% 1.59/0.62    sK0 = sK2 | sK1 = sK2 | sK0 = sK2 | ~spl5_4),
% 1.59/0.62    inference(resolution,[],[f198,f97])).
% 1.59/0.62  fof(f198,plain,(
% 1.59/0.62    r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_4),
% 1.59/0.62    inference(superposition,[],[f96,f121])).
% 1.59/0.62  fof(f121,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl5_4),
% 1.59/0.62    inference(avatar_component_clause,[],[f119])).
% 1.59/0.62  fof(f28,plain,(
% 1.59/0.62    sK0 != sK2),
% 1.59/0.62    inference(cnf_transformation,[],[f22])).
% 1.59/0.62  fof(f249,plain,(
% 1.59/0.62    sK0 = sK1 | ~spl5_4),
% 1.59/0.62    inference(resolution,[],[f222,f96])).
% 1.59/0.62  fof(f222,plain,(
% 1.59/0.62    ( ! [X9] : (~r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK1 = X9) ) | ~spl5_4),
% 1.59/0.62    inference(backward_demodulation,[],[f201,f211])).
% 1.59/0.62  fof(f201,plain,(
% 1.59/0.62    ( ! [X9] : (~r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK2 = X9) ) | ~spl5_4),
% 1.59/0.62    inference(duplicate_literal_removal,[],[f197])).
% 1.59/0.62  fof(f197,plain,(
% 1.59/0.62    ( ! [X9] : (~r2_hidden(X9,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK2 = X9 | sK2 = X9 | sK2 = X9) ) | ~spl5_4),
% 1.59/0.62    inference(superposition,[],[f97,f121])).
% 1.59/0.62  fof(f179,plain,(
% 1.59/0.62    ~spl5_2 | spl5_4),
% 1.59/0.62    inference(avatar_contradiction_clause,[],[f178])).
% 1.59/0.62  fof(f178,plain,(
% 1.59/0.62    $false | (~spl5_2 | spl5_4)),
% 1.59/0.62    inference(subsumption_resolution,[],[f173,f146])).
% 1.59/0.62  fof(f146,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | (~spl5_2 | spl5_4)),
% 1.59/0.62    inference(backward_demodulation,[],[f120,f144])).
% 1.59/0.62  fof(f144,plain,(
% 1.59/0.62    sK1 = sK2 | ~spl5_2),
% 1.59/0.62    inference(subsumption_resolution,[],[f143,f28])).
% 1.59/0.62  fof(f143,plain,(
% 1.59/0.62    sK0 = sK2 | sK1 = sK2 | ~spl5_2),
% 1.59/0.62    inference(duplicate_literal_removal,[],[f142])).
% 1.59/0.62  fof(f142,plain,(
% 1.59/0.62    sK0 = sK2 | sK1 = sK2 | sK0 = sK2 | ~spl5_2),
% 1.59/0.62    inference(resolution,[],[f138,f97])).
% 1.59/0.62  fof(f138,plain,(
% 1.59/0.62    r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_2),
% 1.59/0.62    inference(superposition,[],[f96,f113])).
% 1.59/0.62  fof(f113,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK3) | ~spl5_2),
% 1.59/0.62    inference(avatar_component_clause,[],[f111])).
% 1.59/0.62  fof(f173,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl5_2),
% 1.59/0.62    inference(backward_demodulation,[],[f145,f169])).
% 1.59/0.62  fof(f169,plain,(
% 1.59/0.62    sK1 = sK3 | ~spl5_2),
% 1.59/0.62    inference(subsumption_resolution,[],[f168,f29])).
% 1.59/0.62  fof(f168,plain,(
% 1.59/0.62    sK0 = sK3 | sK1 = sK3 | ~spl5_2),
% 1.59/0.62    inference(duplicate_literal_removal,[],[f167])).
% 1.59/0.62  fof(f167,plain,(
% 1.59/0.62    sK0 = sK3 | sK1 = sK3 | sK0 = sK3 | ~spl5_2),
% 1.59/0.62    inference(resolution,[],[f140,f97])).
% 1.59/0.62  fof(f140,plain,(
% 1.59/0.62    r2_hidden(sK3,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl5_2),
% 1.59/0.62    inference(superposition,[],[f92,f113])).
% 1.59/0.62  fof(f92,plain,(
% 1.59/0.62    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4))) )),
% 1.59/0.62    inference(equality_resolution,[],[f91])).
% 1.59/0.62  fof(f91,plain,(
% 1.59/0.62    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X4) != X3) )),
% 1.59/0.62    inference(equality_resolution,[],[f78])).
% 1.59/0.62  fof(f78,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.59/0.62    inference(definition_unfolding,[],[f54,f59])).
% 1.59/0.62  fof(f54,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.59/0.62    inference(cnf_transformation,[],[f26])).
% 1.59/0.62  fof(f145,plain,(
% 1.59/0.62    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK3) | ~spl5_2),
% 1.59/0.62    inference(backward_demodulation,[],[f113,f144])).
% 1.59/0.62  % SZS output end Proof for theBenchmark
% 1.59/0.62  % (13020)------------------------------
% 1.59/0.62  % (13020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.62  % (13020)Termination reason: Refutation
% 1.59/0.62  
% 1.59/0.62  % (13020)Memory used [KB]: 6396
% 1.59/0.62  % (13020)Time elapsed: 0.209 s
% 1.59/0.62  % (13020)------------------------------
% 1.59/0.62  % (13020)------------------------------
% 1.59/0.63  % (13000)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.59/0.63  % (13001)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.59/0.64  % (12985)Success in time 0.267 s
%------------------------------------------------------------------------------
