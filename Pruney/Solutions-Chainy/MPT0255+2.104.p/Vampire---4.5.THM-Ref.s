%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 666 expanded)
%              Number of leaves         :   29 ( 211 expanded)
%              Depth                    :   18
%              Number of atoms          :  302 (1116 expanded)
%              Number of equality atoms :  151 ( 690 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f741,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f402,f556,f573,f591,f675,f704,f740])).

fof(f740,plain,
    ( ~ spl6_4
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f738])).

fof(f738,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f114,f718])).

fof(f718,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_16 ),
    inference(superposition,[],[f116,f703])).

fof(f703,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f701])).

fof(f701,plain,
    ( spl6_16
  <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f116,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f84,plain,(
    ! [X4,X0] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k3_enumset1(X0,X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f114,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f704,plain,
    ( spl6_16
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f688,f672,f399,f701])).

fof(f399,plain,
    ( spl6_7
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f672,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f688,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f687,f91])).

fof(f91,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f82,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f687,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f686,f521])).

fof(f521,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f520,f190])).

fof(f190,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(global_subsumption,[],[f88,f184])).

fof(f184,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f180,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f180,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f172,f91])).

fof(f172,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[],[f72,f54])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f56,f57,f57])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f520,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f511,f333])).

fof(f333,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f195,f136])).

fof(f136,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(global_subsumption,[],[f88,f134])).

fof(f134,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f75,f64])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f45,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f195,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f58,f190])).

fof(f58,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f511,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f195,f459])).

fof(f459,plain,(
    ! [X2] : k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)) = X2 ),
    inference(forward_demodulation,[],[f458,f91])).

fof(f458,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f457,f333])).

fof(f457,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) ),
    inference(forward_demodulation,[],[f456,f195])).

fof(f456,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)))) ),
    inference(forward_demodulation,[],[f423,f192])).

fof(f192,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f191,f91])).

fof(f191,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f187,f54])).

fof(f187,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f72,f180])).

fof(f423,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X2),k3_xboole_0(k1_xboole_0,X2)))) ),
    inference(superposition,[],[f396,f180])).

fof(f396,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) ),
    inference(forward_demodulation,[],[f74,f58])).

fof(f74,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f43,f69,f57,f69])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f686,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f678,f333])).

fof(f678,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(superposition,[],[f401,f674])).

fof(f674,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f672])).

fof(f401,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f399])).

fof(f675,plain,
    ( spl6_14
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f643,f588,f93,f672])).

fof(f93,plain,
    ( spl6_1
  <=> k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f588,plain,
    ( spl6_10
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f643,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(superposition,[],[f604,f193])).

fof(f193,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f190,f58])).

fof(f604,plain,
    ( ! [X6] : k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),X6))) = X6
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f572,f590])).

fof(f590,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f588])).

fof(f572,plain,
    ( ! [X6] : k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),X6))) = X6
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f165,f333])).

fof(f165,plain,
    ( ! [X6] : k5_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),X6)))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f153,f58])).

fof(f153,plain,
    ( ! [X6] : k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),X6)) = k5_xboole_0(k1_xboole_0,X6)
    | ~ spl6_1 ),
    inference(superposition,[],[f58,f95])).

fof(f95,plain,
    ( k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f591,plain,
    ( spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f585,f415,f588])).

fof(f415,plain,
    ( spl6_8
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f585,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f579,f417])).

fof(f417,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f415])).

fof(f579,plain,
    ( k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl6_8 ),
    inference(superposition,[],[f72,f417])).

fof(f573,plain,
    ( spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f405,f399,f415])).

fof(f405,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl6_7 ),
    inference(superposition,[],[f333,f401])).

fof(f556,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f122,f112])).

fof(f122,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f121,f55])).

fof(f55,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f121,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f119,f88])).

fof(f119,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,X2)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f97,f64])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f60,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f402,plain,
    ( spl6_7
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f358,f93,f399])).

fof(f358,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f329,f91])).

fof(f329,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k1_xboole_0)
    | ~ spl6_1 ),
    inference(superposition,[],[f195,f95])).

fof(f96,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f73,f93])).

fof(f73,plain,(
    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ),
    inference(definition_unfolding,[],[f42,f69,f71])).

fof(f42,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (16879)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (16882)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.50  % (16896)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (16883)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (16884)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (16889)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (16881)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (16894)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (16902)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (16901)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (16890)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (16887)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (16900)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (16905)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (16891)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (16897)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (16885)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (16897)Refutation not found, incomplete strategy% (16897)------------------------------
% 0.21/0.54  % (16897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16897)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16897)Memory used [KB]: 1663
% 0.21/0.54  % (16897)Time elapsed: 0.129 s
% 0.21/0.54  % (16897)------------------------------
% 0.21/0.54  % (16897)------------------------------
% 0.21/0.54  % (16886)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (16888)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (16898)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (16880)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (16905)Refutation not found, incomplete strategy% (16905)------------------------------
% 0.21/0.54  % (16905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16905)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16905)Memory used [KB]: 6268
% 0.21/0.54  % (16905)Time elapsed: 0.139 s
% 0.21/0.54  % (16905)------------------------------
% 0.21/0.54  % (16905)------------------------------
% 0.21/0.54  % (16880)Refutation not found, incomplete strategy% (16880)------------------------------
% 0.21/0.54  % (16880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16880)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16880)Memory used [KB]: 1663
% 0.21/0.54  % (16880)Time elapsed: 0.135 s
% 0.21/0.54  % (16880)------------------------------
% 0.21/0.54  % (16880)------------------------------
% 0.21/0.54  % (16899)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (16895)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (16893)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (16904)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (16907)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (16893)Refutation not found, incomplete strategy% (16893)------------------------------
% 0.21/0.55  % (16893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16893)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16893)Memory used [KB]: 1663
% 0.21/0.55  % (16893)Time elapsed: 0.111 s
% 0.21/0.55  % (16893)------------------------------
% 0.21/0.55  % (16893)------------------------------
% 0.21/0.55  % (16895)Refutation not found, incomplete strategy% (16895)------------------------------
% 0.21/0.55  % (16895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16903)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (16895)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16895)Memory used [KB]: 10618
% 0.21/0.55  % (16895)Time elapsed: 0.149 s
% 0.21/0.55  % (16895)------------------------------
% 0.21/0.55  % (16895)------------------------------
% 0.21/0.55  % (16909)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (16892)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (16909)Refutation not found, incomplete strategy% (16909)------------------------------
% 0.21/0.55  % (16909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16909)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16909)Memory used [KB]: 1663
% 0.21/0.55  % (16909)Time elapsed: 0.001 s
% 0.21/0.55  % (16909)------------------------------
% 0.21/0.55  % (16909)------------------------------
% 0.21/0.55  % (16908)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (16891)Refutation not found, incomplete strategy% (16891)------------------------------
% 0.21/0.55  % (16891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16891)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16891)Memory used [KB]: 10618
% 0.21/0.55  % (16891)Time elapsed: 0.147 s
% 0.21/0.55  % (16891)------------------------------
% 0.21/0.55  % (16891)------------------------------
% 0.21/0.57  % (16902)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f741,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f96,f402,f556,f573,f591,f675,f704,f740])).
% 0.21/0.57  fof(f740,plain,(
% 0.21/0.57    ~spl6_4 | ~spl6_16),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f738])).
% 0.21/0.57  fof(f738,plain,(
% 0.21/0.57    $false | (~spl6_4 | ~spl6_16)),
% 0.21/0.57    inference(subsumption_resolution,[],[f114,f718])).
% 0.21/0.57  fof(f718,plain,(
% 0.21/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl6_16),
% 0.21/0.57    inference(superposition,[],[f116,f703])).
% 0.21/0.57  fof(f703,plain,(
% 0.21/0.57    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | ~spl6_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f701])).
% 0.21/0.57  fof(f701,plain,(
% 0.21/0.57    spl6_16 <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.57    inference(resolution,[],[f84,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(rectify,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ( ! [X4,X0] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X4))) )),
% 0.21/0.57    inference(equality_resolution,[],[f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k3_enumset1(X0,X0,X0,X0,X4) != X2) )),
% 0.21/0.57    inference(equality_resolution,[],[f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 0.21/0.57    inference(definition_unfolding,[],[f48,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f52,f70])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f63,f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(rectify,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(flattening,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0) | ~spl6_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f112])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    spl6_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.57  fof(f704,plain,(
% 0.21/0.57    spl6_16 | ~spl6_7 | ~spl6_14),
% 0.21/0.57    inference(avatar_split_clause,[],[f688,f672,f399,f701])).
% 0.21/0.57  fof(f399,plain,(
% 0.21/0.57    spl6_7 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.57  fof(f672,plain,(
% 0.21/0.57    spl6_14 <=> k1_xboole_0 = sK2),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.57  fof(f688,plain,(
% 0.21/0.57    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | (~spl6_7 | ~spl6_14)),
% 0.21/0.57    inference(forward_demodulation,[],[f687,f91])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(forward_demodulation,[],[f82,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f53,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.57  fof(f687,plain,(
% 0.21/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl6_7 | ~spl6_14)),
% 0.21/0.57    inference(forward_demodulation,[],[f686,f521])).
% 0.21/0.57  fof(f521,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f520,f190])).
% 0.21/0.57  fof(f190,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.57    inference(global_subsumption,[],[f88,f184])).
% 0.21/0.57  fof(f184,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 0.21/0.57    inference(superposition,[],[f180,f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.57  fof(f180,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f172,f91])).
% 0.21/0.57  fof(f172,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)))) )),
% 0.21/0.57    inference(superposition,[],[f72,f54])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f56,f57,f57])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f520,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,X0) = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f511,f333])).
% 0.21/0.57  fof(f333,plain,(
% 0.21/0.57    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.57    inference(superposition,[],[f195,f136])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 0.21/0.57    inference(global_subsumption,[],[f88,f134])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 | ~r1_tarski(X0,X0)) )),
% 0.21/0.57    inference(superposition,[],[f75,f64])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f45,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f44,f57])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.57    inference(rectify,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.57  fof(f195,plain,(
% 0.21/0.57    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2)) )),
% 0.21/0.57    inference(superposition,[],[f58,f190])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.57  fof(f511,plain,(
% 0.21/0.57    ( ! [X0] : (k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.57    inference(superposition,[],[f195,f459])).
% 0.21/0.57  fof(f459,plain,(
% 0.21/0.57    ( ! [X2] : (k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)) = X2) )),
% 0.21/0.57    inference(forward_demodulation,[],[f458,f91])).
% 0.21/0.57  fof(f458,plain,(
% 0.21/0.57    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f457,f333])).
% 0.21/0.57  fof(f457,plain,(
% 0.21/0.57    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f456,f195])).
% 0.21/0.57  fof(f456,plain,(
% 0.21/0.57    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2))))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f423,f192])).
% 0.21/0.57  fof(f192,plain,(
% 0.21/0.57    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 0.21/0.57    inference(forward_demodulation,[],[f191,f91])).
% 0.21/0.57  fof(f191,plain,(
% 0.21/0.57    ( ! [X1] : (k3_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f187,f54])).
% 0.21/0.57  fof(f187,plain,(
% 0.21/0.57    ( ! [X1] : (k3_xboole_0(X1,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.21/0.57    inference(superposition,[],[f72,f180])).
% 0.21/0.57  fof(f423,plain,(
% 0.21/0.57    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X2),k3_xboole_0(k1_xboole_0,X2))))) )),
% 0.21/0.57    inference(superposition,[],[f396,f180])).
% 0.21/0.57  fof(f396,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f74,f58])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f43,f69,f57,f69])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.57  fof(f686,plain,(
% 0.21/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | (~spl6_7 | ~spl6_14)),
% 0.21/0.57    inference(forward_demodulation,[],[f678,f333])).
% 0.21/0.57  fof(f678,plain,(
% 0.21/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) | (~spl6_7 | ~spl6_14)),
% 0.21/0.57    inference(superposition,[],[f401,f674])).
% 0.21/0.57  fof(f674,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | ~spl6_14),
% 0.21/0.57    inference(avatar_component_clause,[],[f672])).
% 0.21/0.57  fof(f401,plain,(
% 0.21/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) | ~spl6_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f399])).
% 0.21/0.57  fof(f675,plain,(
% 0.21/0.57    spl6_14 | ~spl6_1 | ~spl6_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f643,f588,f93,f672])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    spl6_1 <=> k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.57  fof(f588,plain,(
% 0.21/0.57    spl6_10 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.57  fof(f643,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | (~spl6_1 | ~spl6_10)),
% 0.21/0.57    inference(superposition,[],[f604,f193])).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 0.21/0.57    inference(superposition,[],[f190,f58])).
% 0.21/0.57  fof(f604,plain,(
% 0.21/0.57    ( ! [X6] : (k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),X6))) = X6) ) | (~spl6_1 | ~spl6_10)),
% 0.21/0.57    inference(forward_demodulation,[],[f572,f590])).
% 0.21/0.57  fof(f590,plain,(
% 0.21/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl6_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f588])).
% 0.21/0.57  fof(f572,plain,(
% 0.21/0.57    ( ! [X6] : (k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),X6))) = X6) ) | ~spl6_1),
% 0.21/0.57    inference(forward_demodulation,[],[f165,f333])).
% 0.21/0.57  fof(f165,plain,(
% 0.21/0.57    ( ! [X6] : (k5_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),X6)))) ) | ~spl6_1),
% 0.21/0.57    inference(forward_demodulation,[],[f153,f58])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    ( ! [X6] : (k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),X6)) = k5_xboole_0(k1_xboole_0,X6)) ) | ~spl6_1),
% 0.21/0.57    inference(superposition,[],[f58,f95])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) | ~spl6_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f93])).
% 0.21/0.57  fof(f591,plain,(
% 0.21/0.57    spl6_10 | ~spl6_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f585,f415,f588])).
% 0.21/0.57  fof(f415,plain,(
% 0.21/0.57    spl6_8 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.57  fof(f585,plain,(
% 0.21/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl6_8),
% 0.21/0.57    inference(forward_demodulation,[],[f579,f417])).
% 0.21/0.57  fof(f417,plain,(
% 0.21/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl6_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f415])).
% 0.21/0.57  fof(f579,plain,(
% 0.21/0.57    k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl6_8),
% 0.21/0.57    inference(superposition,[],[f72,f417])).
% 0.21/0.57  fof(f573,plain,(
% 0.21/0.57    spl6_8 | ~spl6_7),
% 0.21/0.57    inference(avatar_split_clause,[],[f405,f399,f415])).
% 0.21/0.57  fof(f405,plain,(
% 0.21/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl6_7),
% 0.21/0.57    inference(superposition,[],[f333,f401])).
% 0.21/0.57  fof(f556,plain,(
% 0.21/0.57    spl6_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f122,f112])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f121,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_xboole_0(X0,X0) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(resolution,[],[f119,f88])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~r1_tarski(X1,X2) | ~r1_xboole_0(X1,X2) | v1_xboole_0(X1)) )),
% 0.21/0.57    inference(superposition,[],[f97,f64])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(resolution,[],[f60,f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(rectify,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.57  fof(f402,plain,(
% 0.21/0.57    spl6_7 | ~spl6_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f358,f93,f399])).
% 0.21/0.57  fof(f358,plain,(
% 0.21/0.57    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) | ~spl6_1),
% 0.21/0.57    inference(forward_demodulation,[],[f329,f91])).
% 0.21/0.57  fof(f329,plain,(
% 0.21/0.57    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k1_xboole_0) | ~spl6_1),
% 0.21/0.57    inference(superposition,[],[f195,f95])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    spl6_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f73,f93])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))),
% 0.21/0.57    inference(definition_unfolding,[],[f42,f69,f71])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.58    inference(ennf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.58    inference(negated_conjecture,[],[f20])).
% 0.21/0.58  fof(f20,conjecture,(
% 0.21/0.58    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (16902)------------------------------
% 0.21/0.58  % (16902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (16902)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (16902)Memory used [KB]: 11257
% 0.21/0.58  % (16902)Time elapsed: 0.145 s
% 0.21/0.58  % (16902)------------------------------
% 0.21/0.58  % (16902)------------------------------
% 0.21/0.58  % (16877)Success in time 0.216 s
%------------------------------------------------------------------------------
