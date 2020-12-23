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
% DateTime   : Thu Dec  3 12:41:03 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 561 expanded)
%              Number of leaves         :   27 ( 178 expanded)
%              Depth                    :   19
%              Number of atoms          :  249 ( 899 expanded)
%              Number of equality atoms :   76 ( 416 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f527,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f94,f140,f318,f458,f505,f526])).

fof(f526,plain,
    ( ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f521,f139])).

fof(f139,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_6
  <=> ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f521,plain,
    ( ! [X2] : r2_hidden(sK0,X2)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f518,f266])).

fof(f266,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(trivial_inequality_removal,[],[f257])).

fof(f257,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f53,f237])).

fof(f237,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f222,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f222,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f71,f209])).

fof(f209,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(forward_demodulation,[],[f189,f141])).

fof(f141,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f132,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f132,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k4_xboole_0(X0,X0)) ),
    inference(subsumption_resolution,[],[f127,f95])).

fof(f95,plain,(
    ! [X0] : r1_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f45,f74])).

fof(f74,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(X0,X0))
      | ~ r1_xboole_0(X0,k4_xboole_0(X0,X0)) ) ),
    inference(superposition,[],[f76,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f49])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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

fof(f189,plain,(
    ! [X3] : k4_xboole_0(X3,X3) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f75,f158])).

fof(f158,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f74,f141])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f46,f49,f49])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f518,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,X2)
        | r2_hidden(sK0,X2) )
    | ~ spl4_4 ),
    inference(superposition,[],[f83,f111])).

fof(f111,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_4
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f505,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f503,f92])).

fof(f92,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f503,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_1
    | spl4_4 ),
    inference(duplicate_literal_removal,[],[f502])).

fof(f502,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl4_1
    | spl4_4 ),
    inference(resolution,[],[f476,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f476,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f461,f112])).

fof(f112,plain,
    ( k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f461,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_1 ),
    inference(superposition,[],[f87,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f458,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f456,f91])).

fof(f91,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f456,plain,
    ( r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(resolution,[],[f446,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f69])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f446,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f445])).

fof(f445,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl4_1 ),
    inference(superposition,[],[f88,f392])).

fof(f392,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f372,f41])).

fof(f372,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f71,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f76,f43])).

fof(f88,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f318,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f316,f161])).

fof(f161,plain,(
    ! [X4] : r1_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f45,f141])).

fof(f316,plain,
    ( ! [X8] : ~ r1_xboole_0(k1_xboole_0,X8)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f310,f266])).

fof(f310,plain,
    ( ! [X8] :
        ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ r1_xboole_0(k1_xboole_0,X8) )
    | ~ spl4_5 ),
    inference(superposition,[],[f136,f237])).

fof(f136,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,k4_xboole_0(X2,X3))
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_5
  <=> ! [X3,X2] :
        ( ~ r1_xboole_0(X2,X3)
        | ~ r1_tarski(X2,k4_xboole_0(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f140,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f131,f138,f135])).

fof(f131,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_tarski(X2,k4_xboole_0(X2,X3)) ) ),
    inference(superposition,[],[f76,f54])).

fof(f94,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f73,f90,f86])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f39,f70,f70])).

fof(f39,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( r2_hidden(sK0,sK1)
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( ~ r2_hidden(sK0,sK1)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK0,sK1)
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( ~ r2_hidden(sK0,sK1)
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f93,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f72,f90,f86])).

fof(f72,plain,
    ( r2_hidden(sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f40,f70,f70])).

fof(f40,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:33:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (7571)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (7581)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (7582)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (7589)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (7581)Refutation not found, incomplete strategy% (7581)------------------------------
% 0.21/0.52  % (7581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7581)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7581)Memory used [KB]: 10618
% 0.21/0.52  % (7581)Time elapsed: 0.098 s
% 0.21/0.52  % (7581)------------------------------
% 0.21/0.52  % (7581)------------------------------
% 0.21/0.52  % (7573)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (7577)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (7574)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (7592)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (7578)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (7572)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (7578)Refutation not found, incomplete strategy% (7578)------------------------------
% 0.21/0.54  % (7578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7578)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7578)Memory used [KB]: 10618
% 0.21/0.54  % (7578)Time elapsed: 0.120 s
% 0.21/0.54  % (7578)------------------------------
% 0.21/0.54  % (7578)------------------------------
% 0.21/0.54  % (7584)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (7572)Refutation not found, incomplete strategy% (7572)------------------------------
% 0.21/0.54  % (7572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7572)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7572)Memory used [KB]: 10746
% 0.21/0.54  % (7572)Time elapsed: 0.130 s
% 0.21/0.54  % (7572)------------------------------
% 0.21/0.54  % (7572)------------------------------
% 0.21/0.54  % (7590)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (7588)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (7590)Refutation not found, incomplete strategy% (7590)------------------------------
% 0.21/0.55  % (7590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7592)Refutation not found, incomplete strategy% (7592)------------------------------
% 0.21/0.55  % (7592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7575)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (7592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7592)Memory used [KB]: 10746
% 0.21/0.55  % (7592)Time elapsed: 0.137 s
% 0.21/0.55  % (7592)------------------------------
% 0.21/0.55  % (7592)------------------------------
% 0.21/0.55  % (7596)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (7598)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (7599)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (7590)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7590)Memory used [KB]: 10874
% 0.21/0.56  % (7590)Time elapsed: 0.139 s
% 0.21/0.56  % (7590)------------------------------
% 0.21/0.56  % (7590)------------------------------
% 0.21/0.56  % (7580)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (7585)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (7580)Refutation not found, incomplete strategy% (7580)------------------------------
% 0.21/0.56  % (7580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7580)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7580)Memory used [KB]: 10618
% 0.21/0.56  % (7580)Time elapsed: 0.157 s
% 0.21/0.56  % (7580)------------------------------
% 0.21/0.56  % (7580)------------------------------
% 0.21/0.56  % (7591)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (7591)Refutation not found, incomplete strategy% (7591)------------------------------
% 0.21/0.57  % (7591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7591)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7591)Memory used [KB]: 1791
% 0.21/0.57  % (7591)Time elapsed: 0.133 s
% 0.21/0.57  % (7591)------------------------------
% 0.21/0.57  % (7591)------------------------------
% 0.21/0.57  % (7583)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (7576)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (7570)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (7570)Refutation not found, incomplete strategy% (7570)------------------------------
% 0.21/0.57  % (7570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7570)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7570)Memory used [KB]: 1663
% 0.21/0.57  % (7570)Time elapsed: 0.154 s
% 0.21/0.57  % (7570)------------------------------
% 0.21/0.57  % (7570)------------------------------
% 0.21/0.57  % (7593)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (7594)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.58  % (7585)Refutation not found, incomplete strategy% (7585)------------------------------
% 0.21/0.58  % (7585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (7585)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (7585)Memory used [KB]: 6140
% 0.21/0.58  % (7585)Time elapsed: 0.003 s
% 0.21/0.58  % (7585)------------------------------
% 0.21/0.58  % (7585)------------------------------
% 1.72/0.58  % (7597)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.72/0.58  % (7587)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.72/0.58  % (7587)Refutation not found, incomplete strategy% (7587)------------------------------
% 1.72/0.58  % (7587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.58  % (7587)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.58  
% 1.72/0.58  % (7587)Memory used [KB]: 10618
% 1.72/0.58  % (7587)Time elapsed: 0.164 s
% 1.72/0.58  % (7587)------------------------------
% 1.72/0.58  % (7587)------------------------------
% 1.72/0.58  % (7579)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.72/0.59  % (7579)Refutation not found, incomplete strategy% (7579)------------------------------
% 1.72/0.59  % (7579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.59  % (7579)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.59  
% 1.72/0.59  % (7579)Memory used [KB]: 10618
% 1.72/0.59  % (7579)Time elapsed: 0.160 s
% 1.72/0.59  % (7579)------------------------------
% 1.72/0.59  % (7579)------------------------------
% 1.72/0.59  % (7595)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.72/0.59  % (7586)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.72/0.59  % (7597)Refutation found. Thanks to Tanya!
% 1.72/0.59  % SZS status Theorem for theBenchmark
% 1.72/0.59  % SZS output start Proof for theBenchmark
% 1.72/0.59  fof(f527,plain,(
% 1.72/0.59    $false),
% 1.72/0.59    inference(avatar_sat_refutation,[],[f93,f94,f140,f318,f458,f505,f526])).
% 1.72/0.59  fof(f526,plain,(
% 1.72/0.59    ~spl4_4 | ~spl4_6),
% 1.72/0.59    inference(avatar_contradiction_clause,[],[f524])).
% 1.72/0.59  fof(f524,plain,(
% 1.72/0.59    $false | (~spl4_4 | ~spl4_6)),
% 1.72/0.59    inference(resolution,[],[f521,f139])).
% 1.72/0.59  fof(f139,plain,(
% 1.72/0.59    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) ) | ~spl4_6),
% 1.72/0.59    inference(avatar_component_clause,[],[f138])).
% 1.72/0.59  fof(f138,plain,(
% 1.72/0.59    spl4_6 <=> ! [X4] : ~r2_hidden(X4,k1_xboole_0)),
% 1.72/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.72/0.59  fof(f521,plain,(
% 1.72/0.59    ( ! [X2] : (r2_hidden(sK0,X2)) ) | ~spl4_4),
% 1.72/0.59    inference(subsumption_resolution,[],[f518,f266])).
% 1.72/0.59  fof(f266,plain,(
% 1.72/0.59    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.72/0.59    inference(trivial_inequality_removal,[],[f257])).
% 1.72/0.59  fof(f257,plain,(
% 1.72/0.59    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X1)) )),
% 1.72/0.59    inference(superposition,[],[f53,f237])).
% 1.72/0.59  fof(f237,plain,(
% 1.72/0.59    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.72/0.59    inference(forward_demodulation,[],[f222,f41])).
% 1.72/0.59  fof(f41,plain,(
% 1.72/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.72/0.59    inference(cnf_transformation,[],[f8])).
% 1.72/0.59  fof(f8,axiom,(
% 1.72/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.72/0.59  fof(f222,plain,(
% 1.72/0.59    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.72/0.59    inference(superposition,[],[f71,f209])).
% 1.72/0.59  fof(f209,plain,(
% 1.72/0.59    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f189,f141])).
% 1.72/0.59  fof(f141,plain,(
% 1.72/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.72/0.59    inference(resolution,[],[f132,f43])).
% 1.72/0.59  fof(f43,plain,(
% 1.72/0.59    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.72/0.59    inference(cnf_transformation,[],[f32])).
% 1.72/0.59  fof(f32,plain,(
% 1.72/0.59    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.72/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f31])).
% 1.72/0.59  fof(f31,plain,(
% 1.72/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.72/0.59    introduced(choice_axiom,[])).
% 1.72/0.59  fof(f25,plain,(
% 1.72/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.72/0.59    inference(ennf_transformation,[],[f4])).
% 1.72/0.59  fof(f4,axiom,(
% 1.72/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.72/0.59  fof(f132,plain,(
% 1.72/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0))) )),
% 1.72/0.59    inference(subsumption_resolution,[],[f127,f95])).
% 1.72/0.59  fof(f95,plain,(
% 1.72/0.59    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 1.72/0.59    inference(superposition,[],[f45,f74])).
% 1.72/0.59  fof(f74,plain,(
% 1.72/0.59    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.72/0.59    inference(definition_unfolding,[],[f44,f49])).
% 1.72/0.59  fof(f49,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f7])).
% 1.72/0.59  fof(f7,axiom,(
% 1.72/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.72/0.59  fof(f44,plain,(
% 1.72/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.72/0.59    inference(cnf_transformation,[],[f22])).
% 1.72/0.59  fof(f22,plain,(
% 1.72/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.72/0.59    inference(rectify,[],[f2])).
% 1.72/0.59  fof(f2,axiom,(
% 1.72/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.72/0.59  fof(f45,plain,(
% 1.72/0.59    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f9])).
% 1.72/0.59  fof(f9,axiom,(
% 1.72/0.59    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.72/0.59  fof(f127,plain,(
% 1.72/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0)) | ~r1_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 1.72/0.59    inference(superposition,[],[f76,f74])).
% 1.72/0.59  fof(f76,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.72/0.59    inference(definition_unfolding,[],[f51,f49])).
% 1.72/0.59  fof(f51,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f34])).
% 1.72/0.59  fof(f34,plain,(
% 1.72/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.72/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f33])).
% 1.72/0.59  fof(f33,plain,(
% 1.72/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.72/0.59    introduced(choice_axiom,[])).
% 1.72/0.59  fof(f26,plain,(
% 1.72/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.72/0.59    inference(ennf_transformation,[],[f23])).
% 1.72/0.59  fof(f23,plain,(
% 1.72/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.72/0.59    inference(rectify,[],[f3])).
% 1.72/0.59  fof(f3,axiom,(
% 1.72/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.72/0.59  fof(f189,plain,(
% 1.72/0.59    ( ! [X3] : (k4_xboole_0(X3,X3) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) )),
% 1.72/0.59    inference(superposition,[],[f75,f158])).
% 1.72/0.59  fof(f158,plain,(
% 1.72/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.72/0.59    inference(backward_demodulation,[],[f74,f141])).
% 1.72/0.59  fof(f75,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f46,f49,f49])).
% 1.72/0.59  fof(f46,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f1])).
% 1.72/0.59  fof(f1,axiom,(
% 1.72/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.72/0.59  fof(f71,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f48,f49])).
% 1.72/0.59  fof(f48,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f6])).
% 1.72/0.59  fof(f6,axiom,(
% 1.72/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.72/0.59  fof(f53,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f35])).
% 1.72/0.59  fof(f35,plain,(
% 1.72/0.59    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.72/0.59    inference(nnf_transformation,[],[f5])).
% 1.72/0.59  fof(f5,axiom,(
% 1.72/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.72/0.59  fof(f518,plain,(
% 1.72/0.59    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | r2_hidden(sK0,X2)) ) | ~spl4_4),
% 1.72/0.59    inference(superposition,[],[f83,f111])).
% 1.72/0.59  fof(f111,plain,(
% 1.72/0.59    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_4),
% 1.72/0.59    inference(avatar_component_clause,[],[f110])).
% 1.72/0.59  fof(f110,plain,(
% 1.72/0.59    spl4_4 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.72/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.72/0.59  fof(f83,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.72/0.59    inference(definition_unfolding,[],[f58,f69])).
% 1.72/0.59  fof(f69,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.72/0.59    inference(definition_unfolding,[],[f47,f68])).
% 1.72/0.59  fof(f68,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.72/0.59    inference(definition_unfolding,[],[f57,f67])).
% 1.85/0.61  fof(f67,plain,(
% 1.85/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.85/0.61    inference(definition_unfolding,[],[f61,f66])).
% 1.85/0.61  fof(f66,plain,(
% 1.85/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.85/0.61    inference(definition_unfolding,[],[f62,f65])).
% 1.85/0.61  fof(f65,plain,(
% 1.85/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.85/0.61    inference(definition_unfolding,[],[f63,f64])).
% 1.85/0.61  fof(f64,plain,(
% 1.85/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f16])).
% 1.85/0.61  fof(f16,axiom,(
% 1.85/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.85/0.61  fof(f63,plain,(
% 1.85/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f15])).
% 1.85/0.61  fof(f15,axiom,(
% 1.85/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.85/0.61  fof(f62,plain,(
% 1.85/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f14])).
% 1.85/0.61  fof(f14,axiom,(
% 1.85/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.85/0.61  fof(f61,plain,(
% 1.85/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f13])).
% 1.85/0.61  fof(f13,axiom,(
% 1.85/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.85/0.61  fof(f57,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f12])).
% 1.85/0.61  fof(f12,axiom,(
% 1.85/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.85/0.61  fof(f47,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f11])).
% 1.85/0.61  fof(f11,axiom,(
% 1.85/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.85/0.61  fof(f58,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f38])).
% 1.85/0.61  fof(f38,plain,(
% 1.85/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.85/0.61    inference(flattening,[],[f37])).
% 1.85/0.61  fof(f37,plain,(
% 1.85/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.85/0.61    inference(nnf_transformation,[],[f19])).
% 1.85/0.61  fof(f19,axiom,(
% 1.85/0.61    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.85/0.61  fof(f505,plain,(
% 1.85/0.61    ~spl4_1 | ~spl4_2 | spl4_4),
% 1.85/0.61    inference(avatar_contradiction_clause,[],[f504])).
% 1.85/0.61  fof(f504,plain,(
% 1.85/0.61    $false | (~spl4_1 | ~spl4_2 | spl4_4)),
% 1.85/0.61    inference(subsumption_resolution,[],[f503,f92])).
% 1.85/0.61  fof(f92,plain,(
% 1.85/0.61    r2_hidden(sK0,sK1) | ~spl4_2),
% 1.85/0.61    inference(avatar_component_clause,[],[f90])).
% 1.85/0.61  fof(f90,plain,(
% 1.85/0.61    spl4_2 <=> r2_hidden(sK0,sK1)),
% 1.85/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.85/0.61  fof(f503,plain,(
% 1.85/0.61    ~r2_hidden(sK0,sK1) | (~spl4_1 | spl4_4)),
% 1.85/0.61    inference(duplicate_literal_removal,[],[f502])).
% 1.85/0.61  fof(f502,plain,(
% 1.85/0.61    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,sK1) | (~spl4_1 | spl4_4)),
% 1.85/0.61    inference(resolution,[],[f476,f81])).
% 1.85/0.61  fof(f81,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.85/0.61    inference(definition_unfolding,[],[f60,f69])).
% 1.85/0.61  fof(f60,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f38])).
% 1.85/0.61  fof(f476,plain,(
% 1.85/0.61    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | (~spl4_1 | spl4_4)),
% 1.85/0.61    inference(subsumption_resolution,[],[f461,f112])).
% 1.85/0.61  fof(f112,plain,(
% 1.85/0.61    k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl4_4),
% 1.85/0.61    inference(avatar_component_clause,[],[f110])).
% 1.85/0.61  fof(f461,plain,(
% 1.85/0.61    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_1),
% 1.85/0.61    inference(superposition,[],[f87,f54])).
% 1.85/0.61  fof(f54,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f35])).
% 1.85/0.61  fof(f87,plain,(
% 1.85/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_1),
% 1.85/0.61    inference(avatar_component_clause,[],[f86])).
% 1.85/0.61  fof(f86,plain,(
% 1.85/0.61    spl4_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.85/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.85/0.61  fof(f458,plain,(
% 1.85/0.61    spl4_1 | spl4_2),
% 1.85/0.61    inference(avatar_contradiction_clause,[],[f457])).
% 1.85/0.61  fof(f457,plain,(
% 1.85/0.61    $false | (spl4_1 | spl4_2)),
% 1.85/0.61    inference(subsumption_resolution,[],[f456,f91])).
% 1.85/0.61  fof(f91,plain,(
% 1.85/0.61    ~r2_hidden(sK0,sK1) | spl4_2),
% 1.85/0.61    inference(avatar_component_clause,[],[f90])).
% 1.85/0.61  fof(f456,plain,(
% 1.85/0.61    r2_hidden(sK0,sK1) | spl4_1),
% 1.85/0.61    inference(resolution,[],[f446,f78])).
% 1.85/0.61  fof(f78,plain,(
% 1.85/0.61    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.85/0.61    inference(definition_unfolding,[],[f52,f70])).
% 1.85/0.61  fof(f70,plain,(
% 1.85/0.61    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.85/0.61    inference(definition_unfolding,[],[f42,f69])).
% 1.85/0.61  fof(f42,plain,(
% 1.85/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f10])).
% 1.85/0.61  fof(f10,axiom,(
% 1.85/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.85/0.61  fof(f52,plain,(
% 1.85/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f27])).
% 1.85/0.61  fof(f27,plain,(
% 1.85/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.85/0.61    inference(ennf_transformation,[],[f17])).
% 1.85/0.61  fof(f17,axiom,(
% 1.85/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.85/0.61  fof(f446,plain,(
% 1.85/0.61    ~r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl4_1),
% 1.85/0.61    inference(trivial_inequality_removal,[],[f445])).
% 1.85/0.61  fof(f445,plain,(
% 1.85/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl4_1),
% 1.85/0.61    inference(superposition,[],[f88,f392])).
% 1.85/0.61  fof(f392,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.85/0.61    inference(forward_demodulation,[],[f372,f41])).
% 1.85/0.61  fof(f372,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 1.85/0.61    inference(superposition,[],[f71,f126])).
% 1.85/0.61  fof(f126,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.85/0.61    inference(resolution,[],[f76,f43])).
% 1.85/0.61  fof(f88,plain,(
% 1.85/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl4_1),
% 1.85/0.61    inference(avatar_component_clause,[],[f86])).
% 1.85/0.61  fof(f318,plain,(
% 1.85/0.61    ~spl4_5),
% 1.85/0.61    inference(avatar_contradiction_clause,[],[f317])).
% 1.85/0.61  fof(f317,plain,(
% 1.85/0.61    $false | ~spl4_5),
% 1.85/0.61    inference(subsumption_resolution,[],[f316,f161])).
% 1.85/0.61  fof(f161,plain,(
% 1.85/0.61    ( ! [X4] : (r1_xboole_0(k1_xboole_0,X4)) )),
% 1.85/0.61    inference(superposition,[],[f45,f141])).
% 1.85/0.61  fof(f316,plain,(
% 1.85/0.61    ( ! [X8] : (~r1_xboole_0(k1_xboole_0,X8)) ) | ~spl4_5),
% 1.85/0.61    inference(subsumption_resolution,[],[f310,f266])).
% 1.85/0.61  fof(f310,plain,(
% 1.85/0.61    ( ! [X8] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X8)) ) | ~spl4_5),
% 1.85/0.61    inference(superposition,[],[f136,f237])).
% 1.85/0.61  fof(f136,plain,(
% 1.85/0.61    ( ! [X2,X3] : (~r1_tarski(X2,k4_xboole_0(X2,X3)) | ~r1_xboole_0(X2,X3)) ) | ~spl4_5),
% 1.85/0.61    inference(avatar_component_clause,[],[f135])).
% 1.85/0.62  fof(f135,plain,(
% 1.85/0.62    spl4_5 <=> ! [X3,X2] : (~r1_xboole_0(X2,X3) | ~r1_tarski(X2,k4_xboole_0(X2,X3)))),
% 1.85/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.85/0.62  fof(f140,plain,(
% 1.85/0.62    spl4_5 | spl4_6),
% 1.85/0.62    inference(avatar_split_clause,[],[f131,f138,f135])).
% 1.85/0.62  fof(f131,plain,(
% 1.85/0.62    ( ! [X4,X2,X3] : (~r2_hidden(X4,k1_xboole_0) | ~r1_xboole_0(X2,X3) | ~r1_tarski(X2,k4_xboole_0(X2,X3))) )),
% 1.85/0.62    inference(superposition,[],[f76,f54])).
% 1.85/0.62  fof(f94,plain,(
% 1.85/0.62    spl4_1 | ~spl4_2),
% 1.85/0.62    inference(avatar_split_clause,[],[f73,f90,f86])).
% 1.85/0.62  fof(f73,plain,(
% 1.85/0.62    ~r2_hidden(sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.85/0.62    inference(definition_unfolding,[],[f39,f70,f70])).
% 1.85/0.62  fof(f39,plain,(
% 1.85/0.62    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.85/0.62    inference(cnf_transformation,[],[f30])).
% 1.85/0.62  fof(f30,plain,(
% 1.85/0.62    (r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.85/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 1.85/0.62  fof(f29,plain,(
% 1.85/0.62    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.85/0.62    introduced(choice_axiom,[])).
% 1.85/0.62  fof(f28,plain,(
% 1.85/0.62    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.85/0.62    inference(nnf_transformation,[],[f24])).
% 1.85/0.62  fof(f24,plain,(
% 1.85/0.62    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.85/0.62    inference(ennf_transformation,[],[f21])).
% 1.85/0.62  fof(f21,negated_conjecture,(
% 1.85/0.62    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.85/0.62    inference(negated_conjecture,[],[f20])).
% 1.85/0.62  fof(f20,conjecture,(
% 1.85/0.62    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.85/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.85/0.62  fof(f93,plain,(
% 1.85/0.62    ~spl4_1 | spl4_2),
% 1.85/0.62    inference(avatar_split_clause,[],[f72,f90,f86])).
% 1.85/0.62  fof(f72,plain,(
% 1.85/0.62    r2_hidden(sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.85/0.62    inference(definition_unfolding,[],[f40,f70,f70])).
% 1.85/0.62  fof(f40,plain,(
% 1.85/0.62    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.85/0.62    inference(cnf_transformation,[],[f30])).
% 1.85/0.62  % SZS output end Proof for theBenchmark
% 1.85/0.62  % (7597)------------------------------
% 1.85/0.62  % (7597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.62  % (7597)Termination reason: Refutation
% 1.85/0.62  
% 1.85/0.62  % (7597)Memory used [KB]: 6396
% 1.85/0.62  % (7597)Time elapsed: 0.177 s
% 1.85/0.62  % (7597)------------------------------
% 1.85/0.62  % (7597)------------------------------
% 1.85/0.62  % (7569)Success in time 0.246 s
%------------------------------------------------------------------------------
