%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 231 expanded)
%              Number of leaves         :   16 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  189 ( 486 expanded)
%              Number of equality atoms :   70 ( 260 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f203,f321,f353])).

fof(f353,plain,
    ( spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f350,f256])).

fof(f256,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f255,f82])).

fof(f82,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f255,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) ),
    inference(forward_demodulation,[],[f245,f50])).

fof(f50,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f24,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f245,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | r1_tarski(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f112,f220])).

fof(f220,plain,(
    k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(forward_demodulation,[],[f208,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f208,plain,(
    k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f110,f50])).

fof(f110,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f48,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f31,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f112,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k4_xboole_0(X5,k4_xboole_0(X5,X4))
      | r1_tarski(X4,k4_xboole_0(X4,X5)) ) ),
    inference(superposition,[],[f36,f51])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f350,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f308,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f308,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl2_3
  <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f321,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f319,f88])).

fof(f88,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(resolution,[],[f53,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f319,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl2_3 ),
    inference(subsumption_resolution,[],[f318,f130])).

fof(f130,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f52,f85])).

fof(f85,plain,(
    ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f69,f59])).

fof(f59,plain,(
    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f36,f50])).

fof(f69,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(extensionality_resolution,[],[f35,f49])).

fof(f49,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f26,f47])).

fof(f26,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f318,plain,
    ( r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl2_3 ),
    inference(resolution,[],[f316,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f316,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | spl2_3 ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | ~ r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | spl2_3 ),
    inference(resolution,[],[f309,f52])).

fof(f309,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f307])).

fof(f203,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f189,f78])).

fof(f78,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_1
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f189,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) ),
    inference(trivial_inequality_removal,[],[f185])).

fof(f185,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f36,f158])).

fof(f158,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f146,f105])).

fof(f105,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f98,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f37,f55])).

fof(f98,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f48,f27])).

fof(f146,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f48,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f108,f61])).

fof(f108,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f51,f27])).

fof(f84,plain,
    ( ~ spl2_2
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f66,f76,f80])).

fof(f66,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(extensionality_resolution,[],[f35,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (783056897)
% 0.13/0.38  ipcrm: permission denied for id (783089666)
% 0.13/0.38  ipcrm: permission denied for id (783122435)
% 0.13/0.38  ipcrm: permission denied for id (782696452)
% 0.13/0.38  ipcrm: permission denied for id (783155205)
% 0.13/0.38  ipcrm: permission denied for id (783187974)
% 0.13/0.38  ipcrm: permission denied for id (783220743)
% 0.13/0.38  ipcrm: permission denied for id (783253512)
% 0.13/0.38  ipcrm: permission denied for id (783286281)
% 0.13/0.39  ipcrm: permission denied for id (783351819)
% 0.13/0.39  ipcrm: permission denied for id (783417357)
% 0.13/0.39  ipcrm: permission denied for id (782761999)
% 0.13/0.40  ipcrm: permission denied for id (783777817)
% 0.13/0.40  ipcrm: permission denied for id (783810586)
% 0.13/0.40  ipcrm: permission denied for id (783843355)
% 0.13/0.40  ipcrm: permission denied for id (783876124)
% 0.13/0.40  ipcrm: permission denied for id (783908893)
% 0.20/0.40  ipcrm: permission denied for id (784007198)
% 0.20/0.40  ipcrm: permission denied for id (782827552)
% 0.20/0.41  ipcrm: permission denied for id (784039969)
% 0.20/0.41  ipcrm: permission denied for id (784072738)
% 0.20/0.41  ipcrm: permission denied for id (784105507)
% 0.20/0.41  ipcrm: permission denied for id (784138276)
% 0.20/0.41  ipcrm: permission denied for id (784171045)
% 0.20/0.41  ipcrm: permission denied for id (784203814)
% 0.20/0.41  ipcrm: permission denied for id (784236583)
% 0.20/0.41  ipcrm: permission denied for id (784269352)
% 0.20/0.41  ipcrm: permission denied for id (784302121)
% 0.20/0.41  ipcrm: permission denied for id (784334890)
% 0.20/0.41  ipcrm: permission denied for id (784367659)
% 0.20/0.42  ipcrm: permission denied for id (784695347)
% 0.20/0.42  ipcrm: permission denied for id (782893110)
% 0.20/0.43  ipcrm: permission denied for id (784793656)
% 0.20/0.43  ipcrm: permission denied for id (784859194)
% 0.20/0.43  ipcrm: permission denied for id (784924732)
% 0.20/0.43  ipcrm: permission denied for id (784990270)
% 0.20/0.43  ipcrm: permission denied for id (785055808)
% 0.20/0.43  ipcrm: permission denied for id (785088577)
% 0.20/0.44  ipcrm: permission denied for id (782925891)
% 0.20/0.44  ipcrm: permission denied for id (785154116)
% 0.20/0.44  ipcrm: permission denied for id (785219654)
% 0.20/0.44  ipcrm: permission denied for id (785252423)
% 0.20/0.44  ipcrm: permission denied for id (785285192)
% 0.20/0.44  ipcrm: permission denied for id (785350730)
% 0.20/0.44  ipcrm: permission denied for id (785383499)
% 0.20/0.44  ipcrm: permission denied for id (785547344)
% 0.20/0.45  ipcrm: permission denied for id (785612882)
% 0.20/0.45  ipcrm: permission denied for id (785645651)
% 0.20/0.45  ipcrm: permission denied for id (785743958)
% 0.20/0.45  ipcrm: permission denied for id (785875034)
% 0.20/0.45  ipcrm: permission denied for id (785940572)
% 0.20/0.45  ipcrm: permission denied for id (786006110)
% 0.20/0.46  ipcrm: permission denied for id (786038879)
% 0.20/0.46  ipcrm: permission denied for id (786071648)
% 0.20/0.46  ipcrm: permission denied for id (786137186)
% 0.20/0.46  ipcrm: permission denied for id (786169955)
% 0.20/0.46  ipcrm: permission denied for id (786202724)
% 0.20/0.46  ipcrm: permission denied for id (786235493)
% 0.20/0.46  ipcrm: permission denied for id (786268262)
% 0.20/0.46  ipcrm: permission denied for id (786301031)
% 0.20/0.46  ipcrm: permission denied for id (786333800)
% 0.20/0.46  ipcrm: permission denied for id (786366569)
% 0.20/0.47  ipcrm: permission denied for id (786399338)
% 0.20/0.47  ipcrm: permission denied for id (786432107)
% 0.20/0.47  ipcrm: permission denied for id (786464876)
% 0.20/0.47  ipcrm: permission denied for id (786530414)
% 0.20/0.47  ipcrm: permission denied for id (786595952)
% 0.20/0.47  ipcrm: permission denied for id (786628721)
% 0.20/0.47  ipcrm: permission denied for id (786694259)
% 0.20/0.47  ipcrm: permission denied for id (786727028)
% 0.20/0.47  ipcrm: permission denied for id (786792565)
% 0.20/0.48  ipcrm: permission denied for id (786825334)
% 0.20/0.48  ipcrm: permission denied for id (782991480)
% 0.20/0.48  ipcrm: permission denied for id (786923642)
% 0.20/0.48  ipcrm: permission denied for id (787054718)
% 0.20/0.48  ipcrm: permission denied for id (787087487)
% 0.20/0.60  % (23185)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.61  % (23185)Refutation found. Thanks to Tanya!
% 0.20/0.61  % SZS status Theorem for theBenchmark
% 1.05/0.61  % (23201)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.05/0.61  % (23193)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.05/0.62  % SZS output start Proof for theBenchmark
% 1.05/0.62  fof(f354,plain,(
% 1.05/0.62    $false),
% 1.05/0.62    inference(avatar_sat_refutation,[],[f84,f203,f321,f353])).
% 1.05/0.62  fof(f353,plain,(
% 1.05/0.62    spl2_2 | ~spl2_3),
% 1.05/0.62    inference(avatar_contradiction_clause,[],[f352])).
% 1.05/0.62  fof(f352,plain,(
% 1.05/0.62    $false | (spl2_2 | ~spl2_3)),
% 1.05/0.62    inference(subsumption_resolution,[],[f350,f256])).
% 1.05/0.62  fof(f256,plain,(
% 1.05/0.62    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | spl2_2),
% 1.05/0.62    inference(subsumption_resolution,[],[f255,f82])).
% 1.05/0.62  fof(f82,plain,(
% 1.05/0.62    ~r1_tarski(sK0,k1_xboole_0) | spl2_2),
% 1.05/0.62    inference(avatar_component_clause,[],[f80])).
% 1.05/0.62  fof(f80,plain,(
% 1.05/0.62    spl2_2 <=> r1_tarski(sK0,k1_xboole_0)),
% 1.05/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.05/0.62  fof(f255,plain,(
% 1.05/0.62    r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))),
% 1.05/0.62    inference(forward_demodulation,[],[f245,f50])).
% 1.05/0.62  fof(f50,plain,(
% 1.05/0.62    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.05/0.62    inference(definition_unfolding,[],[f24,f47])).
% 1.05/0.62  fof(f47,plain,(
% 1.05/0.62    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.05/0.62    inference(definition_unfolding,[],[f28,f46])).
% 1.05/0.62  fof(f46,plain,(
% 1.05/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.05/0.62    inference(definition_unfolding,[],[f30,f38])).
% 1.05/0.62  fof(f38,plain,(
% 1.05/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.05/0.62    inference(cnf_transformation,[],[f10])).
% 1.05/0.62  fof(f10,axiom,(
% 1.05/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.05/0.62  fof(f30,plain,(
% 1.05/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.05/0.62    inference(cnf_transformation,[],[f9])).
% 1.05/0.62  fof(f9,axiom,(
% 1.05/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.05/0.62  fof(f28,plain,(
% 1.05/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.05/0.62    inference(cnf_transformation,[],[f8])).
% 1.05/0.62  fof(f8,axiom,(
% 1.05/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.05/0.62  fof(f24,plain,(
% 1.05/0.62    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.05/0.62    inference(cnf_transformation,[],[f17])).
% 1.05/0.62  fof(f17,plain,(
% 1.05/0.62    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.05/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 1.05/0.62  fof(f16,plain,(
% 1.05/0.62    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.05/0.62    introduced(choice_axiom,[])).
% 1.05/0.62  fof(f14,plain,(
% 1.05/0.62    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.05/0.62    inference(ennf_transformation,[],[f13])).
% 1.05/0.62  fof(f13,negated_conjecture,(
% 1.05/0.62    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.05/0.62    inference(negated_conjecture,[],[f12])).
% 1.05/0.62  fof(f12,conjecture,(
% 1.05/0.62    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 1.05/0.62  fof(f245,plain,(
% 1.05/0.62    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | r1_tarski(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.05/0.62    inference(superposition,[],[f112,f220])).
% 1.05/0.62  fof(f220,plain,(
% 1.05/0.62    k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.05/0.62    inference(forward_demodulation,[],[f208,f27])).
% 1.05/0.62  fof(f27,plain,(
% 1.05/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.05/0.62    inference(cnf_transformation,[],[f6])).
% 1.05/0.62  fof(f6,axiom,(
% 1.05/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.05/0.62  fof(f208,plain,(
% 1.05/0.62    k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k4_xboole_0(sK0,k1_xboole_0))),
% 1.05/0.62    inference(superposition,[],[f110,f50])).
% 1.05/0.62  fof(f110,plain,(
% 1.05/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.05/0.62    inference(superposition,[],[f48,f51])).
% 1.05/0.62  fof(f51,plain,(
% 1.05/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.05/0.62    inference(definition_unfolding,[],[f29,f31,f31])).
% 1.05/0.62  fof(f31,plain,(
% 1.05/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.05/0.62    inference(cnf_transformation,[],[f7])).
% 1.05/0.62  fof(f7,axiom,(
% 1.05/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.05/0.62  fof(f29,plain,(
% 1.05/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.05/0.62    inference(cnf_transformation,[],[f1])).
% 1.05/0.62  fof(f1,axiom,(
% 1.05/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.05/0.62  fof(f48,plain,(
% 1.05/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.05/0.62    inference(definition_unfolding,[],[f32,f31])).
% 1.05/0.62  fof(f32,plain,(
% 1.05/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.05/0.62    inference(cnf_transformation,[],[f5])).
% 1.05/0.62  fof(f5,axiom,(
% 1.05/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.05/0.62  fof(f112,plain,(
% 1.05/0.62    ( ! [X4,X5] : (k1_xboole_0 != k4_xboole_0(X5,k4_xboole_0(X5,X4)) | r1_tarski(X4,k4_xboole_0(X4,X5))) )),
% 1.05/0.62    inference(superposition,[],[f36,f51])).
% 1.05/0.62  fof(f36,plain,(
% 1.05/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.05/0.62    inference(cnf_transformation,[],[f20])).
% 1.05/0.62  fof(f20,plain,(
% 1.05/0.62    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.05/0.62    inference(nnf_transformation,[],[f4])).
% 1.05/0.62  fof(f4,axiom,(
% 1.05/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.05/0.62  fof(f350,plain,(
% 1.05/0.62    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | ~spl2_3),
% 1.05/0.62    inference(resolution,[],[f308,f37])).
% 1.05/0.62  fof(f37,plain,(
% 1.05/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.05/0.62    inference(cnf_transformation,[],[f20])).
% 1.05/0.62  fof(f308,plain,(
% 1.05/0.62    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | ~spl2_3),
% 1.05/0.62    inference(avatar_component_clause,[],[f307])).
% 1.05/0.62  fof(f307,plain,(
% 1.05/0.62    spl2_3 <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))),
% 1.05/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.05/0.62  fof(f321,plain,(
% 1.05/0.62    spl2_3),
% 1.05/0.62    inference(avatar_contradiction_clause,[],[f320])).
% 1.05/0.62  fof(f320,plain,(
% 1.05/0.62    $false | spl2_3),
% 1.05/0.62    inference(subsumption_resolution,[],[f319,f88])).
% 1.05/0.62  fof(f88,plain,(
% 1.05/0.62    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))) )),
% 1.05/0.62    inference(resolution,[],[f53,f55])).
% 1.05/0.62  fof(f55,plain,(
% 1.05/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.05/0.62    inference(equality_resolution,[],[f34])).
% 1.05/0.62  fof(f34,plain,(
% 1.05/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.05/0.62    inference(cnf_transformation,[],[f19])).
% 1.05/0.62  fof(f19,plain,(
% 1.05/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.05/0.62    inference(flattening,[],[f18])).
% 1.05/0.62  fof(f18,plain,(
% 1.05/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.05/0.62    inference(nnf_transformation,[],[f3])).
% 1.05/0.62  fof(f3,axiom,(
% 1.05/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.05/0.62  fof(f53,plain,(
% 1.05/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.05/0.62    inference(definition_unfolding,[],[f40,f46])).
% 1.05/0.62  fof(f40,plain,(
% 1.05/0.62    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.05/0.62    inference(cnf_transformation,[],[f22])).
% 1.05/0.62  fof(f22,plain,(
% 1.05/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.05/0.62    inference(flattening,[],[f21])).
% 1.05/0.62  fof(f21,plain,(
% 1.05/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.05/0.62    inference(nnf_transformation,[],[f11])).
% 1.05/0.62  fof(f11,axiom,(
% 1.05/0.62    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.05/0.62  fof(f319,plain,(
% 1.05/0.62    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | spl2_3),
% 1.05/0.62    inference(subsumption_resolution,[],[f318,f130])).
% 1.05/0.62  fof(f130,plain,(
% 1.05/0.62    ~r2_hidden(sK1,sK0)),
% 1.05/0.62    inference(duplicate_literal_removal,[],[f127])).
% 1.05/0.62  fof(f127,plain,(
% 1.05/0.62    ~r2_hidden(sK1,sK0) | ~r2_hidden(sK1,sK0)),
% 1.05/0.62    inference(resolution,[],[f52,f85])).
% 1.05/0.62  fof(f85,plain,(
% 1.05/0.62    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.05/0.62    inference(subsumption_resolution,[],[f69,f59])).
% 1.05/0.62  fof(f59,plain,(
% 1.05/0.62    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.05/0.62    inference(trivial_inequality_removal,[],[f58])).
% 1.05/0.62  fof(f58,plain,(
% 1.05/0.62    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.05/0.62    inference(superposition,[],[f36,f50])).
% 1.05/0.62  fof(f69,plain,(
% 1.05/0.62    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.05/0.62    inference(extensionality_resolution,[],[f35,f49])).
% 1.05/0.62  fof(f49,plain,(
% 1.05/0.62    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.05/0.62    inference(definition_unfolding,[],[f26,f47])).
% 1.05/0.62  fof(f26,plain,(
% 1.05/0.62    sK0 != k1_tarski(sK1)),
% 1.05/0.62    inference(cnf_transformation,[],[f17])).
% 1.05/0.62  fof(f35,plain,(
% 1.05/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.05/0.62    inference(cnf_transformation,[],[f19])).
% 1.05/0.62  fof(f52,plain,(
% 1.05/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.05/0.62    inference(definition_unfolding,[],[f41,f46])).
% 1.05/0.62  fof(f41,plain,(
% 1.05/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.05/0.62    inference(cnf_transformation,[],[f22])).
% 1.05/0.62  fof(f318,plain,(
% 1.05/0.62    r2_hidden(sK1,sK0) | ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | spl2_3),
% 1.05/0.62    inference(resolution,[],[f316,f44])).
% 1.05/0.62  fof(f44,plain,(
% 1.05/0.62    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.05/0.62    inference(cnf_transformation,[],[f23])).
% 1.05/0.62  fof(f23,plain,(
% 1.05/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.05/0.62    inference(nnf_transformation,[],[f15])).
% 1.05/0.62  fof(f15,plain,(
% 1.05/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.05/0.62    inference(ennf_transformation,[],[f2])).
% 1.05/0.62  fof(f2,axiom,(
% 1.05/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.05/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.05/0.62  fof(f316,plain,(
% 1.05/0.62    ~r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | spl2_3),
% 1.05/0.62    inference(duplicate_literal_removal,[],[f315])).
% 1.05/0.62  fof(f315,plain,(
% 1.05/0.62    ~r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | ~r2_hidden(sK1,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | spl2_3),
% 1.05/0.62    inference(resolution,[],[f309,f52])).
% 1.05/0.62  fof(f309,plain,(
% 1.05/0.62    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | spl2_3),
% 1.05/0.62    inference(avatar_component_clause,[],[f307])).
% 1.05/0.62  fof(f203,plain,(
% 1.05/0.62    spl2_1),
% 1.05/0.62    inference(avatar_contradiction_clause,[],[f200])).
% 1.05/0.62  fof(f200,plain,(
% 1.05/0.62    $false | spl2_1),
% 1.05/0.62    inference(resolution,[],[f189,f78])).
% 1.05/0.62  fof(f78,plain,(
% 1.05/0.62    ~r1_tarski(k1_xboole_0,sK0) | spl2_1),
% 1.05/0.62    inference(avatar_component_clause,[],[f76])).
% 1.05/0.62  fof(f76,plain,(
% 1.05/0.62    spl2_1 <=> r1_tarski(k1_xboole_0,sK0)),
% 1.05/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.05/0.62  fof(f189,plain,(
% 1.05/0.62    ( ! [X3] : (r1_tarski(k1_xboole_0,X3)) )),
% 1.05/0.62    inference(trivial_inequality_removal,[],[f185])).
% 1.05/0.62  fof(f185,plain,(
% 1.05/0.62    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X3)) )),
% 1.05/0.62    inference(superposition,[],[f36,f158])).
% 1.05/0.62  fof(f158,plain,(
% 1.05/0.62    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.05/0.62    inference(forward_demodulation,[],[f146,f105])).
% 1.05/0.62  fof(f105,plain,(
% 1.05/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.05/0.62    inference(forward_demodulation,[],[f98,f61])).
% 1.05/0.62  fof(f61,plain,(
% 1.05/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.05/0.62    inference(resolution,[],[f37,f55])).
% 1.05/0.62  fof(f98,plain,(
% 1.05/0.62    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.05/0.62    inference(superposition,[],[f48,f27])).
% 1.05/0.62  fof(f146,plain,(
% 1.05/0.62    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.05/0.62    inference(superposition,[],[f48,f116])).
% 1.05/0.62  fof(f116,plain,(
% 1.05/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.05/0.62    inference(forward_demodulation,[],[f108,f61])).
% 1.05/0.62  fof(f108,plain,(
% 1.05/0.62    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.05/0.62    inference(superposition,[],[f51,f27])).
% 1.05/0.62  fof(f84,plain,(
% 1.05/0.62    ~spl2_2 | ~spl2_1),
% 1.05/0.62    inference(avatar_split_clause,[],[f66,f76,f80])).
% 1.05/0.62  fof(f66,plain,(
% 1.05/0.62    ~r1_tarski(k1_xboole_0,sK0) | ~r1_tarski(sK0,k1_xboole_0)),
% 1.05/0.62    inference(extensionality_resolution,[],[f35,f25])).
% 1.05/0.62  fof(f25,plain,(
% 1.05/0.62    k1_xboole_0 != sK0),
% 1.05/0.62    inference(cnf_transformation,[],[f17])).
% 1.05/0.62  % SZS output end Proof for theBenchmark
% 1.05/0.62  % (23185)------------------------------
% 1.05/0.62  % (23185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.05/0.62  % (23185)Termination reason: Refutation
% 1.05/0.62  
% 1.05/0.62  % (23185)Memory used [KB]: 10874
% 1.05/0.62  % (23185)Time elapsed: 0.082 s
% 1.05/0.62  % (23185)------------------------------
% 1.05/0.62  % (23185)------------------------------
% 1.05/0.62  % (23040)Success in time 0.254 s
%------------------------------------------------------------------------------
