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
% DateTime   : Thu Dec  3 12:38:34 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 689 expanded)
%              Number of leaves         :   29 ( 232 expanded)
%              Depth                    :   21
%              Number of atoms          :  308 (1011 expanded)
%              Number of equality atoms :   73 ( 588 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f877,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f382,f591,f645,f647,f876])).

fof(f876,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f875])).

fof(f875,plain,
    ( $false
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f874,f48])).

fof(f48,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f874,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl6_9 ),
    inference(duplicate_literal_removal,[],[f870])).

fof(f870,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f869,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f869,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl6_9 ),
    inference(trivial_inequality_removal,[],[f867])).

fof(f867,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl6_9 ),
    inference(superposition,[],[f265,f828])).

fof(f828,plain,
    ( ! [X4,X3] :
        ( k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = X4
        | ~ r1_tarski(X3,X4) )
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f827,f84])).

fof(f84,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f50,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f80])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f827,plain,
    ( ! [X4,X3] :
        ( k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = k3_tarski(k3_enumset1(X4,X4,X4,X4,k1_xboole_0))
        | ~ r1_tarski(X3,X4) )
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f519,f767])).

fof(f767,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f760,f92])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f760,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k5_xboole_0(X3,X3)
        | ~ r1_tarski(X3,X3) )
    | ~ spl6_9 ),
    inference(superposition,[],[f753,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f753,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k3_xboole_0(X3,X3))
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f752,f644])).

fof(f644,plain,
    ( ! [X35] : k5_xboole_0(X35,k1_xboole_0) = X35
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f643])).

fof(f643,plain,
    ( spl6_9
  <=> ! [X35] : k5_xboole_0(X35,k1_xboole_0) = X35 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f752,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,X3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f735,f292])).

fof(f292,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) ),
    inference(superposition,[],[f85,f266])).

fof(f266,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f84,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f55,f80,f80])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f81])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f735,plain,(
    ! [X3] :
      ( k5_xboole_0(X3,k3_xboole_0(X3,X3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f548,f66])).

fof(f548,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,k3_xboole_0(X3,X3)) ),
    inference(superposition,[],[f87,f266])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f59,f58,f58,f81])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f519,plain,(
    ! [X4,X3] :
      ( k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3)))
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f88,f66])).

fof(f88,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f60,f81,f58,f81])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f265,plain,(
    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f83,f86])).

fof(f83,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f49,f81,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f647,plain,
    ( spl6_9
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f646,f588,f294,f643])).

fof(f294,plain,
    ( spl6_1
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f588,plain,
    ( spl6_8
  <=> ! [X13,X12] :
        ( k1_xboole_0 = k3_xboole_0(X12,X13)
        | ~ r1_xboole_0(X12,X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f646,plain,
    ( ! [X37] : k5_xboole_0(X37,k1_xboole_0) = X37
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f630,f468])).

fof(f468,plain,
    ( ! [X7] : r1_xboole_0(X7,k1_xboole_0)
    | ~ spl6_1 ),
    inference(resolution,[],[f64,f295])).

fof(f295,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f294])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f630,plain,
    ( ! [X37] :
        ( k5_xboole_0(X37,k1_xboole_0) = X37
        | ~ r1_xboole_0(X37,k1_xboole_0) )
    | ~ spl6_8 ),
    inference(superposition,[],[f524,f589])).

fof(f589,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 = k3_xboole_0(X12,X13)
        | ~ r1_xboole_0(X12,X13) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f588])).

fof(f524,plain,(
    ! [X2] : k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = X2 ),
    inference(forward_demodulation,[],[f520,f266])).

fof(f520,plain,(
    ! [X2] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f88,f266])).

fof(f645,plain,
    ( spl6_2
    | spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f641,f588,f643,f297])).

fof(f297,plain,
    ( spl6_2
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f641,plain,
    ( ! [X35,X36] :
        ( k5_xboole_0(X35,k1_xboole_0) = X35
        | ~ v1_xboole_0(X36) )
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f629,f103])).

fof(f103,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,X3)
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f629,plain,
    ( ! [X35,X36] :
        ( k5_xboole_0(X35,k1_xboole_0) = X35
        | ~ v1_xboole_0(X36)
        | ~ r1_xboole_0(X35,X36) )
    | ~ spl6_8 ),
    inference(superposition,[],[f526,f589])).

fof(f526,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X0)) = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f524,f308])).

fof(f308,plain,(
    ! [X4] :
      ( k1_xboole_0 = X4
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f292,f131])).

fof(f131,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f70,f108])).

fof(f108,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f72,f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f591,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f369,f588])).

fof(f369,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k3_xboole_0(X3,X4)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f305,f109])).

fof(f109,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k3_xboole_0(X4,X5),X6)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f305,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f292,f70])).

fof(f382,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f374,f297,f294])).

fof(f374,plain,
    ( ! [X7] : ~ r2_hidden(X7,k1_xboole_0)
    | ~ spl6_2 ),
    inference(resolution,[],[f306,f328])).

fof(f328,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(X0))
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f97,f298])).

fof(f298,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f297])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f306,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f292,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:49:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (22468)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (22465)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (22473)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (22484)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (22492)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (22466)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (22473)Refutation not found, incomplete strategy% (22473)------------------------------
% 0.21/0.52  % (22473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22489)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (22476)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (22473)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22473)Memory used [KB]: 10618
% 0.21/0.52  % (22473)Time elapsed: 0.115 s
% 0.21/0.52  % (22473)------------------------------
% 0.21/0.52  % (22473)------------------------------
% 0.21/0.53  % (22476)Refutation not found, incomplete strategy% (22476)------------------------------
% 0.21/0.53  % (22476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22476)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22476)Memory used [KB]: 10618
% 0.21/0.53  % (22476)Time elapsed: 0.135 s
% 0.21/0.53  % (22476)------------------------------
% 0.21/0.53  % (22476)------------------------------
% 0.21/0.53  % (22470)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (22488)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (22467)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (22469)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (22467)Refutation not found, incomplete strategy% (22467)------------------------------
% 0.21/0.53  % (22467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22467)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22467)Memory used [KB]: 10618
% 0.21/0.53  % (22467)Time elapsed: 0.123 s
% 0.21/0.53  % (22467)------------------------------
% 0.21/0.53  % (22467)------------------------------
% 0.21/0.53  % (22478)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (22475)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (22475)Refutation not found, incomplete strategy% (22475)------------------------------
% 0.21/0.54  % (22475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22475)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22475)Memory used [KB]: 10618
% 0.21/0.54  % (22475)Time elapsed: 0.138 s
% 0.21/0.54  % (22475)------------------------------
% 0.21/0.54  % (22475)------------------------------
% 0.21/0.54  % (22471)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (22494)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (22477)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (22491)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (22486)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (22480)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (22493)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (22483)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (22485)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (22472)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.54/0.56  % (22481)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.54/0.57  % (22474)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.54/0.57  % (22482)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.54/0.57  % (22490)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.54/0.57  % (22487)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.54/0.57  % (22479)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.54/0.57  % (22487)Refutation not found, incomplete strategy% (22487)------------------------------
% 1.54/0.57  % (22487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (22487)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (22487)Memory used [KB]: 10746
% 1.54/0.57  % (22487)Time elapsed: 0.141 s
% 1.54/0.57  % (22487)------------------------------
% 1.54/0.57  % (22487)------------------------------
% 1.63/0.59  % (22492)Refutation found. Thanks to Tanya!
% 1.63/0.59  % SZS status Theorem for theBenchmark
% 1.63/0.59  % SZS output start Proof for theBenchmark
% 1.63/0.59  fof(f877,plain,(
% 1.63/0.59    $false),
% 1.63/0.59    inference(avatar_sat_refutation,[],[f382,f591,f645,f647,f876])).
% 1.63/0.59  fof(f876,plain,(
% 1.63/0.59    ~spl6_9),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f875])).
% 1.63/0.59  fof(f875,plain,(
% 1.63/0.59    $false | ~spl6_9),
% 1.63/0.59    inference(subsumption_resolution,[],[f874,f48])).
% 1.63/0.59  fof(f48,plain,(
% 1.63/0.59    r2_hidden(sK0,sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f31,plain,(
% 1.63/0.59    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f30])).
% 1.63/0.59  fof(f30,plain,(
% 1.63/0.59    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f24,plain,(
% 1.63/0.59    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.63/0.59    inference(ennf_transformation,[],[f21])).
% 1.63/0.59  fof(f21,negated_conjecture,(
% 1.63/0.59    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.63/0.59    inference(negated_conjecture,[],[f20])).
% 1.63/0.59  fof(f20,conjecture,(
% 1.63/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.63/0.59  fof(f874,plain,(
% 1.63/0.59    ~r2_hidden(sK0,sK1) | ~spl6_9),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f870])).
% 1.63/0.59  fof(f870,plain,(
% 1.63/0.59    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,sK1) | ~spl6_9),
% 1.63/0.59    inference(resolution,[],[f869,f89])).
% 1.63/0.59  fof(f89,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f77,f80])).
% 1.63/0.59  fof(f80,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f56,f79])).
% 1.63/0.59  fof(f79,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f74,f78])).
% 1.63/0.59  fof(f78,plain,(
% 1.63/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f17])).
% 1.63/0.59  fof(f17,axiom,(
% 1.63/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.63/0.59  fof(f74,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f16])).
% 1.63/0.59  fof(f16,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.63/0.59  fof(f56,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f15])).
% 1.63/0.59  fof(f15,axiom,(
% 1.63/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.63/0.59  fof(f77,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f47])).
% 1.63/0.59  fof(f47,plain,(
% 1.63/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.63/0.59    inference(flattening,[],[f46])).
% 1.63/0.59  fof(f46,plain,(
% 1.63/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.63/0.59    inference(nnf_transformation,[],[f19])).
% 1.63/0.59  fof(f19,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.63/0.59  fof(f869,plain,(
% 1.63/0.59    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl6_9),
% 1.63/0.59    inference(trivial_inequality_removal,[],[f867])).
% 1.63/0.59  fof(f867,plain,(
% 1.63/0.59    sK1 != sK1 | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl6_9),
% 1.63/0.59    inference(superposition,[],[f265,f828])).
% 1.63/0.59  fof(f828,plain,(
% 1.63/0.59    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = X4 | ~r1_tarski(X3,X4)) ) | ~spl6_9),
% 1.63/0.59    inference(forward_demodulation,[],[f827,f84])).
% 1.63/0.59  fof(f84,plain,(
% 1.63/0.59    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.63/0.59    inference(definition_unfolding,[],[f50,f81])).
% 1.63/0.59  fof(f81,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.63/0.59    inference(definition_unfolding,[],[f57,f80])).
% 1.63/0.59  fof(f57,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f18])).
% 1.63/0.59  fof(f18,axiom,(
% 1.63/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.63/0.59  fof(f50,plain,(
% 1.63/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.59    inference(cnf_transformation,[],[f8])).
% 1.63/0.59  fof(f8,axiom,(
% 1.63/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.63/0.59  fof(f827,plain,(
% 1.63/0.59    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = k3_tarski(k3_enumset1(X4,X4,X4,X4,k1_xboole_0)) | ~r1_tarski(X3,X4)) ) | ~spl6_9),
% 1.63/0.59    inference(forward_demodulation,[],[f519,f767])).
% 1.63/0.59  fof(f767,plain,(
% 1.63/0.59    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) ) | ~spl6_9),
% 1.63/0.59    inference(subsumption_resolution,[],[f760,f92])).
% 1.63/0.59  fof(f92,plain,(
% 1.63/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.63/0.59    inference(equality_resolution,[],[f69])).
% 1.63/0.59  fof(f69,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.63/0.59    inference(cnf_transformation,[],[f41])).
% 1.63/0.59  fof(f41,plain,(
% 1.63/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.59    inference(flattening,[],[f40])).
% 1.63/0.59  fof(f40,plain,(
% 1.63/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.59    inference(nnf_transformation,[],[f6])).
% 1.63/0.59  fof(f6,axiom,(
% 1.63/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.63/0.59  fof(f760,plain,(
% 1.63/0.59    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3) | ~r1_tarski(X3,X3)) ) | ~spl6_9),
% 1.63/0.59    inference(superposition,[],[f753,f66])).
% 1.63/0.59  fof(f66,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f27])).
% 1.63/0.59  fof(f27,plain,(
% 1.63/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.63/0.59    inference(ennf_transformation,[],[f9])).
% 1.63/0.59  fof(f9,axiom,(
% 1.63/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.63/0.59  fof(f753,plain,(
% 1.63/0.59    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k3_xboole_0(X3,X3))) ) | ~spl6_9),
% 1.63/0.59    inference(forward_demodulation,[],[f752,f644])).
% 1.63/0.59  fof(f644,plain,(
% 1.63/0.59    ( ! [X35] : (k5_xboole_0(X35,k1_xboole_0) = X35) ) | ~spl6_9),
% 1.63/0.59    inference(avatar_component_clause,[],[f643])).
% 1.63/0.59  fof(f643,plain,(
% 1.63/0.59    spl6_9 <=> ! [X35] : k5_xboole_0(X35,k1_xboole_0) = X35),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.63/0.59  fof(f752,plain,(
% 1.63/0.59    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,X3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f735,f292])).
% 1.63/0.59  fof(f292,plain,(
% 1.63/0.59    ( ! [X3] : (r1_tarski(k1_xboole_0,X3)) )),
% 1.63/0.59    inference(superposition,[],[f85,f266])).
% 1.63/0.59  fof(f266,plain,(
% 1.63/0.59    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.63/0.59    inference(superposition,[],[f84,f86])).
% 1.63/0.59  fof(f86,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f55,f80,f80])).
% 1.63/0.59  fof(f55,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f13])).
% 1.63/0.59  fof(f13,axiom,(
% 1.63/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.63/0.59  fof(f85,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.63/0.59    inference(definition_unfolding,[],[f54,f81])).
% 1.63/0.59  fof(f54,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f12])).
% 1.63/0.59  fof(f12,axiom,(
% 1.63/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.63/0.59  fof(f735,plain,(
% 1.63/0.59    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,X3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X3)) )),
% 1.63/0.59    inference(superposition,[],[f548,f66])).
% 1.63/0.59  fof(f548,plain,(
% 1.63/0.59    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,k3_xboole_0(X3,X3))) )),
% 1.63/0.59    inference(superposition,[],[f87,f266])).
% 1.63/0.59  fof(f87,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.63/0.59    inference(definition_unfolding,[],[f59,f58,f58,f81])).
% 1.63/0.59  fof(f58,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f7])).
% 1.63/0.59  fof(f7,axiom,(
% 1.63/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.63/0.59  fof(f59,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f11])).
% 1.63/0.59  fof(f11,axiom,(
% 1.63/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.63/0.59  fof(f519,plain,(
% 1.63/0.59    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) | ~r1_tarski(X3,X4)) )),
% 1.63/0.59    inference(superposition,[],[f88,f66])).
% 1.63/0.59  fof(f88,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.63/0.59    inference(definition_unfolding,[],[f60,f81,f58,f81])).
% 1.63/0.59  fof(f60,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f10])).
% 1.63/0.59  fof(f10,axiom,(
% 1.63/0.59    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.63/0.59  fof(f265,plain,(
% 1.63/0.59    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.63/0.59    inference(backward_demodulation,[],[f83,f86])).
% 1.63/0.59  fof(f83,plain,(
% 1.63/0.59    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.63/0.59    inference(definition_unfolding,[],[f49,f81,f82])).
% 1.63/0.59  fof(f82,plain,(
% 1.63/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f51,f80])).
% 1.63/0.59  fof(f51,plain,(
% 1.63/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f14])).
% 1.63/0.59  fof(f14,axiom,(
% 1.63/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.63/0.59  fof(f49,plain,(
% 1.63/0.59    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f647,plain,(
% 1.63/0.59    spl6_9 | ~spl6_1 | ~spl6_8),
% 1.63/0.59    inference(avatar_split_clause,[],[f646,f588,f294,f643])).
% 1.63/0.59  fof(f294,plain,(
% 1.63/0.59    spl6_1 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.63/0.59  fof(f588,plain,(
% 1.63/0.59    spl6_8 <=> ! [X13,X12] : (k1_xboole_0 = k3_xboole_0(X12,X13) | ~r1_xboole_0(X12,X13))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.63/0.59  fof(f646,plain,(
% 1.63/0.59    ( ! [X37] : (k5_xboole_0(X37,k1_xboole_0) = X37) ) | (~spl6_1 | ~spl6_8)),
% 1.63/0.59    inference(subsumption_resolution,[],[f630,f468])).
% 1.63/0.59  fof(f468,plain,(
% 1.63/0.59    ( ! [X7] : (r1_xboole_0(X7,k1_xboole_0)) ) | ~spl6_1),
% 1.63/0.59    inference(resolution,[],[f64,f295])).
% 1.63/0.59  fof(f295,plain,(
% 1.63/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_1),
% 1.63/0.59    inference(avatar_component_clause,[],[f294])).
% 1.63/0.59  fof(f64,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f39])).
% 1.63/0.59  fof(f39,plain,(
% 1.63/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f38])).
% 1.63/0.59  fof(f38,plain,(
% 1.63/0.59    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f26,plain,(
% 1.63/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.63/0.59    inference(ennf_transformation,[],[f23])).
% 1.63/0.59  fof(f23,plain,(
% 1.63/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.63/0.59    inference(rectify,[],[f4])).
% 1.63/0.59  fof(f4,axiom,(
% 1.63/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.63/0.59  fof(f630,plain,(
% 1.63/0.59    ( ! [X37] : (k5_xboole_0(X37,k1_xboole_0) = X37 | ~r1_xboole_0(X37,k1_xboole_0)) ) | ~spl6_8),
% 1.63/0.59    inference(superposition,[],[f524,f589])).
% 1.63/0.59  fof(f589,plain,(
% 1.63/0.59    ( ! [X12,X13] : (k1_xboole_0 = k3_xboole_0(X12,X13) | ~r1_xboole_0(X12,X13)) ) | ~spl6_8),
% 1.63/0.59    inference(avatar_component_clause,[],[f588])).
% 1.63/0.59  fof(f524,plain,(
% 1.63/0.59    ( ! [X2] : (k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = X2) )),
% 1.63/0.59    inference(forward_demodulation,[],[f520,f266])).
% 1.63/0.59  fof(f520,plain,(
% 1.63/0.59    ( ! [X2] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0))) )),
% 1.63/0.59    inference(superposition,[],[f88,f266])).
% 1.63/0.59  fof(f645,plain,(
% 1.63/0.59    spl6_2 | spl6_9 | ~spl6_8),
% 1.63/0.59    inference(avatar_split_clause,[],[f641,f588,f643,f297])).
% 1.63/0.59  fof(f297,plain,(
% 1.63/0.59    spl6_2 <=> ! [X0] : ~v1_xboole_0(X0)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.63/0.59  fof(f641,plain,(
% 1.63/0.59    ( ! [X35,X36] : (k5_xboole_0(X35,k1_xboole_0) = X35 | ~v1_xboole_0(X36)) ) | ~spl6_8),
% 1.63/0.59    inference(subsumption_resolution,[],[f629,f103])).
% 1.63/0.59  fof(f103,plain,(
% 1.63/0.59    ( ! [X2,X3] : (r1_xboole_0(X2,X3) | ~v1_xboole_0(X3)) )),
% 1.63/0.59    inference(resolution,[],[f64,f52])).
% 1.63/0.59  fof(f52,plain,(
% 1.63/0.59    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f35])).
% 1.63/0.59  fof(f35,plain,(
% 1.63/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 1.63/0.59  fof(f34,plain,(
% 1.63/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f33,plain,(
% 1.63/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.63/0.59    inference(rectify,[],[f32])).
% 1.63/0.59  fof(f32,plain,(
% 1.63/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.63/0.59    inference(nnf_transformation,[],[f2])).
% 1.63/0.59  fof(f2,axiom,(
% 1.63/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.63/0.59  fof(f629,plain,(
% 1.63/0.59    ( ! [X35,X36] : (k5_xboole_0(X35,k1_xboole_0) = X35 | ~v1_xboole_0(X36) | ~r1_xboole_0(X35,X36)) ) | ~spl6_8),
% 1.63/0.59    inference(superposition,[],[f526,f589])).
% 1.63/0.59  fof(f526,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X0)) = X1 | ~v1_xboole_0(X0)) )),
% 1.63/0.59    inference(superposition,[],[f524,f308])).
% 1.63/0.59  fof(f308,plain,(
% 1.63/0.59    ( ! [X4] : (k1_xboole_0 = X4 | ~v1_xboole_0(X4)) )),
% 1.63/0.59    inference(resolution,[],[f292,f131])).
% 1.63/0.59  fof(f131,plain,(
% 1.63/0.59    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~v1_xboole_0(X2)) )),
% 1.63/0.59    inference(resolution,[],[f70,f108])).
% 1.63/0.59  fof(f108,plain,(
% 1.63/0.59    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v1_xboole_0(X2)) )),
% 1.63/0.59    inference(resolution,[],[f72,f52])).
% 1.63/0.59  fof(f72,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f45])).
% 1.63/0.59  fof(f45,plain,(
% 1.63/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).
% 1.63/0.59  fof(f44,plain,(
% 1.63/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f43,plain,(
% 1.63/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.63/0.59    inference(rectify,[],[f42])).
% 1.63/0.59  fof(f42,plain,(
% 1.63/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.63/0.59    inference(nnf_transformation,[],[f29])).
% 1.63/0.59  fof(f29,plain,(
% 1.63/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f3])).
% 1.63/0.59  fof(f3,axiom,(
% 1.63/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.63/0.59  fof(f70,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f41])).
% 1.63/0.59  fof(f591,plain,(
% 1.63/0.59    spl6_8),
% 1.63/0.59    inference(avatar_split_clause,[],[f369,f588])).
% 1.63/0.59  fof(f369,plain,(
% 1.63/0.59    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X3,X4) | ~r1_xboole_0(X3,X4)) )),
% 1.63/0.59    inference(resolution,[],[f305,f109])).
% 1.63/0.59  fof(f109,plain,(
% 1.63/0.59    ( ! [X6,X4,X5] : (r1_tarski(k3_xboole_0(X4,X5),X6) | ~r1_xboole_0(X4,X5)) )),
% 1.63/0.59    inference(resolution,[],[f72,f62])).
% 1.63/0.59  fof(f62,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f37])).
% 1.63/0.59  fof(f37,plain,(
% 1.63/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f36])).
% 1.63/0.59  fof(f36,plain,(
% 1.63/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f25,plain,(
% 1.63/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.63/0.59    inference(ennf_transformation,[],[f22])).
% 1.63/0.59  fof(f22,plain,(
% 1.63/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.63/0.59    inference(rectify,[],[f5])).
% 1.63/0.59  fof(f5,axiom,(
% 1.63/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.63/0.59  fof(f305,plain,(
% 1.63/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.63/0.59    inference(resolution,[],[f292,f70])).
% 1.63/0.59  fof(f382,plain,(
% 1.63/0.59    spl6_1 | ~spl6_2),
% 1.63/0.59    inference(avatar_split_clause,[],[f374,f297,f294])).
% 1.63/0.59  fof(f374,plain,(
% 1.63/0.59    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0)) ) | ~spl6_2),
% 1.63/0.59    inference(resolution,[],[f306,f328])).
% 1.63/0.59  fof(f328,plain,(
% 1.63/0.59    ( ! [X0] : (~r2_hidden(X0,sK2(X0))) ) | ~spl6_2),
% 1.63/0.59    inference(subsumption_resolution,[],[f97,f298])).
% 1.63/0.59  fof(f298,plain,(
% 1.63/0.59    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl6_2),
% 1.63/0.59    inference(avatar_component_clause,[],[f297])).
% 1.63/0.59  fof(f97,plain,(
% 1.63/0.59    ( ! [X0] : (~r2_hidden(X0,sK2(X0)) | v1_xboole_0(X0)) )),
% 1.63/0.59    inference(resolution,[],[f67,f53])).
% 1.63/0.59  fof(f53,plain,(
% 1.63/0.59    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f35])).
% 1.63/0.59  fof(f67,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f28])).
% 1.63/0.59  fof(f28,plain,(
% 1.63/0.59    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.63/0.59    inference(ennf_transformation,[],[f1])).
% 1.63/0.59  fof(f1,axiom,(
% 1.63/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.63/0.59  fof(f306,plain,(
% 1.63/0.59    ( ! [X2,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.63/0.59    inference(resolution,[],[f292,f71])).
% 1.63/0.59  fof(f71,plain,(
% 1.63/0.59    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f45])).
% 1.63/0.59  % SZS output end Proof for theBenchmark
% 1.63/0.59  % (22492)------------------------------
% 1.63/0.59  % (22492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (22492)Termination reason: Refutation
% 1.63/0.59  
% 1.63/0.59  % (22492)Memory used [KB]: 6524
% 1.63/0.59  % (22492)Time elapsed: 0.167 s
% 1.63/0.59  % (22492)------------------------------
% 1.63/0.59  % (22492)------------------------------
% 1.63/0.59  % (22464)Success in time 0.232 s
%------------------------------------------------------------------------------
