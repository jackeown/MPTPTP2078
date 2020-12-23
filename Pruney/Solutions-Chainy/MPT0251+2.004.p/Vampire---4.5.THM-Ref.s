%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:35 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 286 expanded)
%              Number of leaves         :   28 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  293 ( 603 expanded)
%              Number of equality atoms :   63 ( 198 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f597,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f152,f180,f589,f596])).

fof(f596,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f176,f136])).

fof(f136,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f176,plain,
    ( ! [X3] : ~ v1_xboole_0(X3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_3
  <=> ! [X3] : ~ v1_xboole_0(X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f589,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f587,f256])).

fof(f256,plain,(
    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f86,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f55,f83,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f72,plain,(
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

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f86,plain,(
    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f49,f84,f85])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f83])).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f83])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f49,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f587,plain,
    ( sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f586,f87])).

fof(f87,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f51,f84])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f586,plain,
    ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k1_xboole_0))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f573,f242])).

fof(f242,plain,
    ( ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f241,f107])).

fof(f107,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f63,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f241,plain,
    ( ! [X5] : k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,X5))
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f239,f181])).

fof(f181,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f87,f88])).

fof(f239,plain,
    ( ! [X5] : k1_xboole_0 = k5_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X5)),k3_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X5)),X5))
    | ~ spl6_4 ),
    inference(resolution,[],[f90,f179])).

fof(f179,plain,
    ( ! [X2] : r1_xboole_0(k1_xboole_0,X2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl6_4
  <=> ! [X2] : r1_xboole_0(k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0 ) ),
    inference(definition_unfolding,[],[f65,f58,f84])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f573,plain,(
    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f89,f482])).

fof(f482,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(resolution,[],[f142,f48])).

fof(f48,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f142,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3) ) ),
    inference(resolution,[],[f91,f63])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f85])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f89,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f59,f84,f58,f84])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f180,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f167,f178,f175])).

fof(f167,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k1_xboole_0,X2)
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f131,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
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

fof(f131,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(k1_xboole_0,X1),X2)
      | r1_xboole_0(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f128,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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

fof(f128,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f74,f108])).

fof(f108,plain,(
    ! [X0] : sP0(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f95,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f63,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f95,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f152,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f148,f145])).

fof(f145,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | ~ spl6_2 ),
    inference(resolution,[],[f139,f53])).

fof(f139,plain,
    ( ! [X0] : r2_hidden(sK3(k1_xboole_0),X0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_2
  <=> ! [X0] : r2_hidden(sK3(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f148,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl6_2 ),
    inference(resolution,[],[f139,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f66,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
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

fof(f140,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f130,f138,f134])).

fof(f130,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_xboole_0),X0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f128,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:42:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.51  % (5971)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.53  % (5977)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.53  % (5965)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.53  % (5964)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.53  % (5988)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.53  % (5967)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.53  % (5969)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.54  % (5968)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.54  % (5992)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.54  % (5979)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.54  % (5991)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.54  % (5978)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.54  % (5993)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.54  % (5986)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.54  % (5966)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.54  % (5978)Refutation not found, incomplete strategy% (5978)------------------------------
% 0.23/0.54  % (5978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (5983)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.55  % (5978)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (5978)Memory used [KB]: 1663
% 0.23/0.55  % (5978)Time elapsed: 0.091 s
% 0.23/0.55  % (5978)------------------------------
% 0.23/0.55  % (5978)------------------------------
% 0.23/0.55  % (5992)Refutation not found, incomplete strategy% (5992)------------------------------
% 0.23/0.55  % (5992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (5980)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.55  % (5965)Refutation not found, incomplete strategy% (5965)------------------------------
% 0.23/0.55  % (5965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (5984)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.55  % (5965)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (5965)Memory used [KB]: 1663
% 0.23/0.55  % (5965)Time elapsed: 0.133 s
% 0.23/0.55  % (5965)------------------------------
% 0.23/0.55  % (5965)------------------------------
% 0.23/0.55  % (5985)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.55  % (5972)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.55  % (5973)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.55  % (5975)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.55  % (5982)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.55  % (5992)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (5992)Memory used [KB]: 10746
% 0.23/0.55  % (5992)Time elapsed: 0.140 s
% 0.23/0.55  % (5992)------------------------------
% 0.23/0.55  % (5992)------------------------------
% 0.23/0.56  % (5970)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.56  % (5976)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.56  % (5989)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.56  % (5976)Refutation not found, incomplete strategy% (5976)------------------------------
% 0.23/0.56  % (5976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (5976)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (5976)Memory used [KB]: 10618
% 0.23/0.56  % (5976)Time elapsed: 0.149 s
% 0.23/0.56  % (5976)------------------------------
% 0.23/0.56  % (5976)------------------------------
% 0.23/0.56  % (5974)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.56  % (5993)Refutation not found, incomplete strategy% (5993)------------------------------
% 0.23/0.56  % (5993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (5993)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (5993)Memory used [KB]: 1663
% 0.23/0.56  % (5993)Time elapsed: 0.149 s
% 0.23/0.56  % (5993)------------------------------
% 0.23/0.56  % (5993)------------------------------
% 0.23/0.56  % (5990)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.56  % (5980)Refutation not found, incomplete strategy% (5980)------------------------------
% 0.23/0.56  % (5980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (5980)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (5980)Memory used [KB]: 10618
% 0.23/0.56  % (5980)Time elapsed: 0.146 s
% 0.23/0.56  % (5980)------------------------------
% 0.23/0.56  % (5980)------------------------------
% 0.23/0.56  % (5981)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.57  % (5974)Refutation not found, incomplete strategy% (5974)------------------------------
% 0.23/0.57  % (5974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (5974)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (5974)Memory used [KB]: 10746
% 0.23/0.57  % (5974)Time elapsed: 0.157 s
% 0.23/0.57  % (5974)------------------------------
% 0.23/0.57  % (5974)------------------------------
% 0.23/0.57  % (5981)Refutation not found, incomplete strategy% (5981)------------------------------
% 0.23/0.57  % (5981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (5981)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (5981)Memory used [KB]: 1663
% 0.23/0.57  % (5981)Time elapsed: 0.128 s
% 0.23/0.57  % (5981)------------------------------
% 0.23/0.57  % (5981)------------------------------
% 0.23/0.57  % (5987)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.59  % (5970)Refutation found. Thanks to Tanya!
% 0.23/0.59  % SZS status Theorem for theBenchmark
% 0.23/0.59  % SZS output start Proof for theBenchmark
% 0.23/0.59  fof(f597,plain,(
% 0.23/0.59    $false),
% 0.23/0.59    inference(avatar_sat_refutation,[],[f140,f152,f180,f589,f596])).
% 0.23/0.59  fof(f596,plain,(
% 0.23/0.59    ~spl6_1 | ~spl6_3),
% 0.23/0.59    inference(avatar_contradiction_clause,[],[f593])).
% 0.23/0.59  fof(f593,plain,(
% 0.23/0.59    $false | (~spl6_1 | ~spl6_3)),
% 0.23/0.59    inference(resolution,[],[f176,f136])).
% 0.23/0.59  fof(f136,plain,(
% 0.23/0.59    v1_xboole_0(k1_xboole_0) | ~spl6_1),
% 0.23/0.59    inference(avatar_component_clause,[],[f134])).
% 0.23/0.59  fof(f134,plain,(
% 0.23/0.59    spl6_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.23/0.59  fof(f176,plain,(
% 0.23/0.59    ( ! [X3] : (~v1_xboole_0(X3)) ) | ~spl6_3),
% 0.23/0.59    inference(avatar_component_clause,[],[f175])).
% 0.23/0.59  fof(f175,plain,(
% 0.23/0.59    spl6_3 <=> ! [X3] : ~v1_xboole_0(X3)),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.23/0.59  fof(f589,plain,(
% 0.23/0.59    ~spl6_4),
% 0.23/0.59    inference(avatar_contradiction_clause,[],[f588])).
% 0.23/0.59  fof(f588,plain,(
% 0.23/0.59    $false | ~spl6_4),
% 0.23/0.59    inference(subsumption_resolution,[],[f587,f256])).
% 0.23/0.59  fof(f256,plain,(
% 0.23/0.59    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.23/0.59    inference(forward_demodulation,[],[f86,f88])).
% 0.23/0.59  fof(f88,plain,(
% 0.23/0.59    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 0.23/0.59    inference(definition_unfolding,[],[f55,f83,f83])).
% 0.23/0.59  fof(f83,plain,(
% 0.23/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.23/0.59    inference(definition_unfolding,[],[f56,f82])).
% 0.23/0.59  fof(f82,plain,(
% 0.23/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.23/0.59    inference(definition_unfolding,[],[f72,f81])).
% 0.23/0.59  fof(f81,plain,(
% 0.23/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f17])).
% 0.23/0.59  fof(f17,axiom,(
% 0.23/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.59  fof(f72,plain,(
% 0.23/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f16])).
% 0.23/0.59  fof(f16,axiom,(
% 0.23/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.59  fof(f56,plain,(
% 0.23/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f15])).
% 0.23/0.59  fof(f15,axiom,(
% 0.23/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.59  fof(f55,plain,(
% 0.23/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f13])).
% 0.23/0.59  fof(f13,axiom,(
% 0.23/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.23/0.59  fof(f86,plain,(
% 0.23/0.59    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))),
% 0.23/0.59    inference(definition_unfolding,[],[f49,f84,f85])).
% 0.23/0.59  fof(f85,plain,(
% 0.23/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.23/0.59    inference(definition_unfolding,[],[f52,f83])).
% 0.23/0.59  fof(f52,plain,(
% 0.23/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f14])).
% 0.23/0.59  fof(f14,axiom,(
% 0.23/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.59  fof(f84,plain,(
% 0.23/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.23/0.59    inference(definition_unfolding,[],[f57,f83])).
% 0.23/0.59  fof(f57,plain,(
% 0.23/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.23/0.59    inference(cnf_transformation,[],[f19])).
% 0.23/0.59  fof(f19,axiom,(
% 0.23/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.23/0.60  fof(f49,plain,(
% 0.23/0.60    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 0.23/0.60    inference(cnf_transformation,[],[f32])).
% 0.23/0.60  fof(f32,plain,(
% 0.23/0.60    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2)),
% 0.23/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f31])).
% 0.23/0.60  fof(f31,plain,(
% 0.23/0.60    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2))),
% 0.23/0.60    introduced(choice_axiom,[])).
% 0.23/0.60  fof(f23,plain,(
% 0.23/0.60    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.23/0.60    inference(ennf_transformation,[],[f21])).
% 0.23/0.60  fof(f21,negated_conjecture,(
% 0.23/0.60    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.23/0.60    inference(negated_conjecture,[],[f20])).
% 0.23/0.60  fof(f20,conjecture,(
% 0.23/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.23/0.60  fof(f587,plain,(
% 0.23/0.60    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl6_4),
% 0.23/0.60    inference(forward_demodulation,[],[f586,f87])).
% 0.23/0.60  fof(f87,plain,(
% 0.23/0.60    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.23/0.60    inference(definition_unfolding,[],[f51,f84])).
% 0.23/0.60  fof(f51,plain,(
% 0.23/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.60    inference(cnf_transformation,[],[f8])).
% 0.23/0.60  fof(f8,axiom,(
% 0.23/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.23/0.60  fof(f586,plain,(
% 0.23/0.60    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k1_xboole_0)) | ~spl6_4),
% 0.23/0.60    inference(forward_demodulation,[],[f573,f242])).
% 0.23/0.60  fof(f242,plain,(
% 0.23/0.60    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) ) | ~spl6_4),
% 0.23/0.60    inference(forward_demodulation,[],[f241,f107])).
% 0.23/0.60  fof(f107,plain,(
% 0.23/0.60    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 0.23/0.60    inference(resolution,[],[f63,f93])).
% 0.23/0.60  fof(f93,plain,(
% 0.23/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.60    inference(equality_resolution,[],[f68])).
% 0.23/0.60  fof(f68,plain,(
% 0.23/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.60    inference(cnf_transformation,[],[f40])).
% 0.23/0.60  fof(f40,plain,(
% 0.23/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.60    inference(flattening,[],[f39])).
% 0.23/0.60  fof(f39,plain,(
% 0.23/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.60    inference(nnf_transformation,[],[f6])).
% 0.23/0.60  fof(f6,axiom,(
% 0.23/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.60  fof(f63,plain,(
% 0.23/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.23/0.60    inference(cnf_transformation,[],[f25])).
% 0.23/0.60  fof(f25,plain,(
% 0.23/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.60    inference(ennf_transformation,[],[f9])).
% 0.23/0.60  fof(f9,axiom,(
% 0.23/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.60  fof(f241,plain,(
% 0.23/0.60    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,X5))) ) | ~spl6_4),
% 0.23/0.60    inference(forward_demodulation,[],[f239,f181])).
% 0.23/0.60  fof(f181,plain,(
% 0.23/0.60    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 0.23/0.60    inference(superposition,[],[f87,f88])).
% 0.23/0.60  fof(f239,plain,(
% 0.23/0.60    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X5)),k3_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X5)),X5))) ) | ~spl6_4),
% 0.23/0.60    inference(resolution,[],[f90,f179])).
% 0.23/0.60  fof(f179,plain,(
% 0.23/0.60    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) ) | ~spl6_4),
% 0.23/0.60    inference(avatar_component_clause,[],[f178])).
% 0.23/0.60  fof(f178,plain,(
% 0.23/0.60    spl6_4 <=> ! [X2] : r1_xboole_0(k1_xboole_0,X2)),
% 0.23/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.23/0.60  fof(f90,plain,(
% 0.23/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0) )),
% 0.23/0.60    inference(definition_unfolding,[],[f65,f58,f84])).
% 0.23/0.60  fof(f58,plain,(
% 0.23/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.60    inference(cnf_transformation,[],[f7])).
% 0.23/0.60  fof(f7,axiom,(
% 0.23/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.60  fof(f65,plain,(
% 0.23/0.60    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f27])).
% 0.23/0.60  fof(f27,plain,(
% 0.23/0.60    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.23/0.60    inference(ennf_transformation,[],[f12])).
% 0.23/0.60  fof(f12,axiom,(
% 0.23/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.23/0.60  fof(f573,plain,(
% 0.23/0.60    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 0.23/0.60    inference(superposition,[],[f89,f482])).
% 0.23/0.60  fof(f482,plain,(
% 0.23/0.60    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 0.23/0.60    inference(resolution,[],[f142,f48])).
% 0.23/0.60  fof(f48,plain,(
% 0.23/0.60    r2_hidden(sK1,sK2)),
% 0.23/0.60    inference(cnf_transformation,[],[f32])).
% 0.23/0.60  fof(f142,plain,(
% 0.23/0.60    ( ! [X2,X3] : (~r2_hidden(X2,X3) | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3)) )),
% 0.23/0.60    inference(resolution,[],[f91,f63])).
% 0.23/0.60  fof(f91,plain,(
% 0.23/0.60    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.60    inference(definition_unfolding,[],[f71,f85])).
% 0.23/0.60  fof(f71,plain,(
% 0.23/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f41])).
% 0.23/0.60  fof(f41,plain,(
% 0.23/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.23/0.60    inference(nnf_transformation,[],[f18])).
% 0.23/0.60  fof(f18,axiom,(
% 0.23/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.23/0.60  fof(f89,plain,(
% 0.23/0.60    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.23/0.60    inference(definition_unfolding,[],[f59,f84,f58,f84])).
% 0.23/0.60  fof(f59,plain,(
% 0.23/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f11])).
% 0.23/0.60  fof(f11,axiom,(
% 0.23/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.23/0.60  fof(f180,plain,(
% 0.23/0.60    spl6_3 | spl6_4),
% 0.23/0.60    inference(avatar_split_clause,[],[f167,f178,f175])).
% 0.23/0.60  fof(f167,plain,(
% 0.23/0.60    ( ! [X2,X3] : (r1_xboole_0(k1_xboole_0,X2) | ~v1_xboole_0(X3)) )),
% 0.23/0.60    inference(resolution,[],[f131,f53])).
% 0.23/0.60  fof(f53,plain,(
% 0.23/0.60    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f36])).
% 0.23/0.60  fof(f36,plain,(
% 0.23/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.23/0.60  fof(f35,plain,(
% 0.23/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.23/0.60    introduced(choice_axiom,[])).
% 0.23/0.60  fof(f34,plain,(
% 0.23/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.60    inference(rectify,[],[f33])).
% 0.23/0.60  fof(f33,plain,(
% 0.23/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.60    inference(nnf_transformation,[],[f2])).
% 0.23/0.60  fof(f2,axiom,(
% 0.23/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.23/0.60  fof(f131,plain,(
% 0.23/0.60    ( ! [X2,X1] : (r2_hidden(sK4(k1_xboole_0,X1),X2) | r1_xboole_0(k1_xboole_0,X1)) )),
% 0.23/0.60    inference(resolution,[],[f128,f60])).
% 0.23/0.60  fof(f60,plain,(
% 0.23/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f38])).
% 0.23/0.60  fof(f38,plain,(
% 0.23/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.23/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f37])).
% 0.23/0.60  fof(f37,plain,(
% 0.23/0.60    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.23/0.60    introduced(choice_axiom,[])).
% 0.23/0.60  fof(f24,plain,(
% 0.23/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.23/0.60    inference(ennf_transformation,[],[f22])).
% 0.23/0.60  fof(f22,plain,(
% 0.23/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.60    inference(rectify,[],[f5])).
% 0.23/0.60  fof(f5,axiom,(
% 0.23/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.23/0.60  fof(f128,plain,(
% 0.23/0.60    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,X4)) )),
% 0.23/0.60    inference(resolution,[],[f74,f108])).
% 0.23/0.60  fof(f108,plain,(
% 0.23/0.60    ( ! [X0] : (sP0(X0,k1_xboole_0,k1_xboole_0)) )),
% 0.23/0.60    inference(superposition,[],[f95,f106])).
% 0.23/0.60  fof(f106,plain,(
% 0.23/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.23/0.60    inference(resolution,[],[f63,f50])).
% 0.23/0.60  fof(f50,plain,(
% 0.23/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f10])).
% 0.23/0.60  fof(f10,axiom,(
% 0.23/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.23/0.60  fof(f95,plain,(
% 0.23/0.60    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.60    inference(equality_resolution,[],[f79])).
% 0.23/0.60  fof(f79,plain,(
% 0.23/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.23/0.60    inference(cnf_transformation,[],[f47])).
% 0.23/0.60  fof(f47,plain,(
% 0.23/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.23/0.60    inference(nnf_transformation,[],[f30])).
% 0.23/0.60  fof(f30,plain,(
% 0.23/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.23/0.60    inference(definition_folding,[],[f3,f29])).
% 0.23/0.60  fof(f29,plain,(
% 0.23/0.60    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.23/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.23/0.60  fof(f3,axiom,(
% 0.23/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.23/0.60  fof(f74,plain,(
% 0.23/0.60    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f46])).
% 0.23/0.60  fof(f46,plain,(
% 0.23/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.23/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 0.23/0.60  fof(f45,plain,(
% 0.23/0.60    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.23/0.60    introduced(choice_axiom,[])).
% 0.23/0.60  fof(f44,plain,(
% 0.23/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.23/0.60    inference(rectify,[],[f43])).
% 0.23/0.60  fof(f43,plain,(
% 0.23/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.23/0.60    inference(flattening,[],[f42])).
% 0.23/0.60  fof(f42,plain,(
% 0.23/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.23/0.60    inference(nnf_transformation,[],[f29])).
% 0.23/0.60  fof(f152,plain,(
% 0.23/0.60    ~spl6_2),
% 0.23/0.60    inference(avatar_contradiction_clause,[],[f151])).
% 0.23/0.60  fof(f151,plain,(
% 0.23/0.60    $false | ~spl6_2),
% 0.23/0.60    inference(subsumption_resolution,[],[f148,f145])).
% 0.23/0.60  fof(f145,plain,(
% 0.23/0.60    ( ! [X1] : (~v1_xboole_0(X1)) ) | ~spl6_2),
% 0.23/0.60    inference(resolution,[],[f139,f53])).
% 0.23/0.60  fof(f139,plain,(
% 0.23/0.60    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0),X0)) ) | ~spl6_2),
% 0.23/0.60    inference(avatar_component_clause,[],[f138])).
% 0.23/0.60  fof(f138,plain,(
% 0.23/0.60    spl6_2 <=> ! [X0] : r2_hidden(sK3(k1_xboole_0),X0)),
% 0.23/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.23/0.60  fof(f148,plain,(
% 0.23/0.60    v1_xboole_0(sK3(k1_xboole_0)) | ~spl6_2),
% 0.23/0.60    inference(resolution,[],[f139,f99])).
% 0.23/0.60  fof(f99,plain,(
% 0.23/0.60    ( ! [X0] : (~r2_hidden(X0,sK3(X0)) | v1_xboole_0(X0)) )),
% 0.23/0.60    inference(resolution,[],[f66,f54])).
% 0.23/0.60  fof(f54,plain,(
% 0.23/0.60    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f36])).
% 0.23/0.60  fof(f66,plain,(
% 0.23/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f28])).
% 0.23/0.60  fof(f28,plain,(
% 0.23/0.60    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.23/0.60    inference(ennf_transformation,[],[f1])).
% 0.23/0.60  fof(f1,axiom,(
% 0.23/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.23/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.23/0.60  fof(f140,plain,(
% 0.23/0.60    spl6_1 | spl6_2),
% 0.23/0.60    inference(avatar_split_clause,[],[f130,f138,f134])).
% 0.23/0.60  fof(f130,plain,(
% 0.23/0.60    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0),X0) | v1_xboole_0(k1_xboole_0)) )),
% 0.23/0.60    inference(resolution,[],[f128,f54])).
% 0.23/0.60  % SZS output end Proof for theBenchmark
% 0.23/0.60  % (5970)------------------------------
% 0.23/0.60  % (5970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.60  % (5970)Termination reason: Refutation
% 0.23/0.60  
% 0.23/0.60  % (5970)Memory used [KB]: 11001
% 0.23/0.60  % (5970)Time elapsed: 0.145 s
% 0.23/0.60  % (5970)------------------------------
% 0.23/0.60  % (5970)------------------------------
% 0.23/0.60  % (5963)Success in time 0.229 s
%------------------------------------------------------------------------------
