%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:33 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 194 expanded)
%              Number of leaves         :   19 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  212 ( 453 expanded)
%              Number of equality atoms :   40 ( 119 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2397,f2804,f3140,f3210,f3245])).

fof(f3245,plain,
    ( ~ spl5_27
    | spl5_53 ),
    inference(avatar_contradiction_clause,[],[f3239])).

fof(f3239,plain,
    ( $false
    | ~ spl5_27
    | spl5_53 ),
    inference(resolution,[],[f3174,f2718])).

fof(f2718,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_27 ),
    inference(trivial_inequality_removal,[],[f2674])).

fof(f2674,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK0)
    | ~ spl5_27 ),
    inference(superposition,[],[f164,f1881])).

fof(f1881,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f1879])).

fof(f1879,plain,
    ( spl5_27
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f164,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k4_xboole_0(X5,k4_xboole_0(X5,X4))
      | r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f62,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f39,f41,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f3174,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_53 ),
    inference(avatar_component_clause,[],[f3172])).

fof(f3172,plain,
    ( spl5_53
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f3210,plain,
    ( ~ spl5_42
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f452,f3172,f2362])).

fof(f2362,plain,
    ( spl5_42
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f452,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f445,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f445,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f439,f34])).

fof(f34,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f439,plain,(
    ! [X6,X7] :
      ( r1_xboole_0(X6,X7)
      | ~ r1_xboole_0(X7,X6) ) ),
    inference(trivial_inequality_removal,[],[f419])).

fof(f419,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X6,X7)
      | ~ r1_xboole_0(X7,X6) ) ),
    inference(superposition,[],[f62,f157])).

fof(f157,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,X4))
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f61,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3140,plain,(
    ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f3134])).

fof(f3134,plain,
    ( $false
    | ~ spl5_28 ),
    inference(resolution,[],[f3118,f33])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f3118,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ spl5_28 ),
    inference(resolution,[],[f2836,f244])).

fof(f244,plain,(
    ! [X19,X20,X18] :
      ( r1_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X19)),X20)
      | ~ r1_xboole_0(X20,X19) ) ),
    inference(resolution,[],[f77,f165])).

fof(f165,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) ),
    inference(superposition,[],[f37,f61])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_xboole_0(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f56,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f2836,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl5_28 ),
    inference(resolution,[],[f1885,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1885,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f1883])).

fof(f1883,plain,
    ( spl5_28
  <=> r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f2804,plain,
    ( spl5_27
    | spl5_28 ),
    inference(avatar_split_clause,[],[f2784,f1883,f1879])).

fof(f2784,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f1306,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f133])).

fof(f133,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = X4
      | ~ r1_xboole_0(X4,X4)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f48,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f63,f48])).

fof(f1306,plain,(
    ! [X0] :
      ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f196,f60])).

fof(f60,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f31,f41,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f196,plain,(
    ! [X12,X10,X11] :
      ( ~ r1_tarski(X12,k2_enumset1(X11,X11,X11,X11))
      | r1_xboole_0(X12,X10)
      | r2_hidden(X11,X10) ) ),
    inference(superposition,[],[f56,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f2397,plain,(
    spl5_42 ),
    inference(avatar_contradiction_clause,[],[f2391])).

fof(f2391,plain,
    ( $false
    | spl5_42 ),
    inference(resolution,[],[f2390,f33])).

fof(f2390,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl5_42 ),
    inference(resolution,[],[f2364,f439])).

fof(f2364,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_42 ),
    inference(avatar_component_clause,[],[f2362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (29103)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (29107)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (29106)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (29098)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (29094)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (29096)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (29097)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (29095)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (29093)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (29104)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (29108)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (29099)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (29092)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (29100)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (29102)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (29105)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (29101)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % (29109)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.61/0.56  % (29096)Refutation found. Thanks to Tanya!
% 1.61/0.56  % SZS status Theorem for theBenchmark
% 1.61/0.56  % SZS output start Proof for theBenchmark
% 1.61/0.56  fof(f3246,plain,(
% 1.61/0.56    $false),
% 1.61/0.56    inference(avatar_sat_refutation,[],[f2397,f2804,f3140,f3210,f3245])).
% 1.61/0.56  fof(f3245,plain,(
% 1.61/0.56    ~spl5_27 | spl5_53),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f3239])).
% 1.61/0.56  fof(f3239,plain,(
% 1.61/0.56    $false | (~spl5_27 | spl5_53)),
% 1.61/0.56    inference(resolution,[],[f3174,f2718])).
% 1.61/0.56  fof(f2718,plain,(
% 1.61/0.56    r1_xboole_0(sK1,sK0) | ~spl5_27),
% 1.61/0.56    inference(trivial_inequality_removal,[],[f2674])).
% 1.61/0.56  fof(f2674,plain,(
% 1.61/0.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK0) | ~spl5_27),
% 1.61/0.56    inference(superposition,[],[f164,f1881])).
% 1.61/0.56  fof(f1881,plain,(
% 1.61/0.56    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_27),
% 1.61/0.56    inference(avatar_component_clause,[],[f1879])).
% 1.61/0.56  fof(f1879,plain,(
% 1.61/0.56    spl5_27 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.61/0.56  fof(f164,plain,(
% 1.61/0.56    ( ! [X4,X5] : (k1_xboole_0 != k4_xboole_0(X5,k4_xboole_0(X5,X4)) | r1_xboole_0(X4,X5)) )),
% 1.61/0.56    inference(superposition,[],[f62,f61])).
% 1.61/0.56  fof(f61,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.61/0.56    inference(definition_unfolding,[],[f39,f41,f41])).
% 1.61/0.56  fof(f41,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.61/0.56    inference(cnf_transformation,[],[f6])).
% 1.61/0.56  fof(f6,axiom,(
% 1.61/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.61/0.56  fof(f39,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f1])).
% 1.61/0.56  fof(f1,axiom,(
% 1.61/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.61/0.56  fof(f62,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.61/0.56    inference(definition_unfolding,[],[f47,f41])).
% 1.61/0.56  fof(f47,plain,(
% 1.61/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.61/0.56    inference(cnf_transformation,[],[f28])).
% 1.61/0.56  fof(f28,plain,(
% 1.61/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.61/0.56    inference(nnf_transformation,[],[f2])).
% 1.61/0.56  fof(f2,axiom,(
% 1.61/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.61/0.56  fof(f3174,plain,(
% 1.61/0.56    ~r1_xboole_0(sK1,sK0) | spl5_53),
% 1.61/0.56    inference(avatar_component_clause,[],[f3172])).
% 1.61/0.56  fof(f3172,plain,(
% 1.61/0.56    spl5_53 <=> r1_xboole_0(sK1,sK0)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 1.61/0.56  fof(f3210,plain,(
% 1.61/0.56    ~spl5_42 | ~spl5_53),
% 1.61/0.56    inference(avatar_split_clause,[],[f452,f3172,f2362])).
% 1.61/0.56  fof(f2362,plain,(
% 1.61/0.56    spl5_42 <=> r1_xboole_0(sK1,sK2)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.61/0.56  fof(f452,plain,(
% 1.61/0.56    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 1.61/0.56    inference(resolution,[],[f445,f53])).
% 1.61/0.56  fof(f53,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f22])).
% 1.61/0.56  fof(f22,plain,(
% 1.61/0.56    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.61/0.56    inference(ennf_transformation,[],[f8])).
% 1.61/0.56  fof(f8,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.61/0.56  fof(f445,plain,(
% 1.61/0.56    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.61/0.56    inference(resolution,[],[f439,f34])).
% 1.61/0.56  fof(f34,plain,(
% 1.61/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.61/0.56    inference(cnf_transformation,[],[f25])).
% 1.61/0.56  fof(f25,plain,(
% 1.61/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24])).
% 1.61/0.56  fof(f24,plain,(
% 1.61/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f20,plain,(
% 1.61/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.61/0.56    inference(flattening,[],[f19])).
% 1.61/0.56  fof(f19,plain,(
% 1.61/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.61/0.56    inference(ennf_transformation,[],[f17])).
% 1.61/0.56  fof(f17,negated_conjecture,(
% 1.61/0.56    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.61/0.56    inference(negated_conjecture,[],[f16])).
% 1.61/0.56  fof(f16,conjecture,(
% 1.61/0.56    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.61/0.56  fof(f439,plain,(
% 1.61/0.56    ( ! [X6,X7] : (r1_xboole_0(X6,X7) | ~r1_xboole_0(X7,X6)) )),
% 1.61/0.56    inference(trivial_inequality_removal,[],[f419])).
% 1.61/0.56  fof(f419,plain,(
% 1.61/0.56    ( ! [X6,X7] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X6,X7) | ~r1_xboole_0(X7,X6)) )),
% 1.61/0.56    inference(superposition,[],[f62,f157])).
% 1.61/0.56  fof(f157,plain,(
% 1.61/0.56    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,X4)) | ~r1_xboole_0(X4,X5)) )),
% 1.61/0.56    inference(superposition,[],[f61,f63])).
% 1.61/0.56  fof(f63,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.61/0.56    inference(definition_unfolding,[],[f46,f41])).
% 1.61/0.56  fof(f46,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f28])).
% 1.61/0.56  fof(f3140,plain,(
% 1.61/0.56    ~spl5_28),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f3134])).
% 1.61/0.56  fof(f3134,plain,(
% 1.61/0.56    $false | ~spl5_28),
% 1.61/0.56    inference(resolution,[],[f3118,f33])).
% 1.61/0.56  fof(f33,plain,(
% 1.61/0.56    r1_xboole_0(sK2,sK1)),
% 1.61/0.56    inference(cnf_transformation,[],[f25])).
% 1.61/0.56  fof(f3118,plain,(
% 1.61/0.56    ~r1_xboole_0(sK2,sK1) | ~spl5_28),
% 1.61/0.56    inference(resolution,[],[f2836,f244])).
% 1.61/0.56  fof(f244,plain,(
% 1.61/0.56    ( ! [X19,X20,X18] : (r1_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X19)),X20) | ~r1_xboole_0(X20,X19)) )),
% 1.61/0.56    inference(resolution,[],[f77,f165])).
% 1.61/0.56  fof(f165,plain,(
% 1.61/0.56    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6)) )),
% 1.61/0.56    inference(superposition,[],[f37,f61])).
% 1.61/0.56  fof(f37,plain,(
% 1.61/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f5])).
% 1.61/0.56  fof(f5,axiom,(
% 1.61/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.61/0.56  fof(f77,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_xboole_0(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.61/0.56    inference(superposition,[],[f56,f48])).
% 1.61/0.56  fof(f48,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f29])).
% 1.61/0.56  fof(f29,plain,(
% 1.61/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.61/0.56    inference(nnf_transformation,[],[f10])).
% 1.61/0.56  fof(f10,axiom,(
% 1.61/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.61/0.56  fof(f56,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f23])).
% 1.61/0.56  fof(f23,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.61/0.56    inference(ennf_transformation,[],[f11])).
% 1.61/0.56  fof(f11,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.61/0.56  fof(f2836,plain,(
% 1.61/0.56    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) | ~spl5_28),
% 1.61/0.56    inference(resolution,[],[f1885,f100])).
% 1.61/0.56  fof(f100,plain,(
% 1.61/0.56    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 1.61/0.56    inference(resolution,[],[f45,f32])).
% 1.61/0.56  fof(f32,plain,(
% 1.61/0.56    r2_hidden(sK3,sK2)),
% 1.61/0.56    inference(cnf_transformation,[],[f25])).
% 1.61/0.56  fof(f45,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f27])).
% 1.61/0.56  fof(f27,plain,(
% 1.61/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f26])).
% 1.61/0.56  fof(f26,plain,(
% 1.61/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f21,plain,(
% 1.61/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.61/0.56    inference(ennf_transformation,[],[f18])).
% 1.61/0.56  fof(f18,plain,(
% 1.61/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.61/0.56    inference(rectify,[],[f3])).
% 1.61/0.56  fof(f3,axiom,(
% 1.61/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.61/0.56  fof(f1885,plain,(
% 1.61/0.56    r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl5_28),
% 1.61/0.56    inference(avatar_component_clause,[],[f1883])).
% 1.61/0.56  fof(f1883,plain,(
% 1.61/0.56    spl5_28 <=> r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.61/0.56  fof(f2804,plain,(
% 1.61/0.56    spl5_27 | spl5_28),
% 1.61/0.56    inference(avatar_split_clause,[],[f2784,f1883,f1879])).
% 1.61/0.56  fof(f2784,plain,(
% 1.61/0.56    r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.61/0.56    inference(resolution,[],[f1306,f145])).
% 1.61/0.56  fof(f145,plain,(
% 1.61/0.56    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.61/0.56    inference(condensation,[],[f133])).
% 1.61/0.56  fof(f133,plain,(
% 1.61/0.56    ( ! [X4,X5] : (k1_xboole_0 = X4 | ~r1_xboole_0(X4,X4) | ~r1_xboole_0(X4,X5)) )),
% 1.61/0.56    inference(superposition,[],[f48,f117])).
% 1.61/0.56  fof(f117,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.61/0.56    inference(duplicate_literal_removal,[],[f106])).
% 1.61/0.56  fof(f106,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X0) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.61/0.56    inference(superposition,[],[f63,f48])).
% 1.61/0.56  fof(f1306,plain,(
% 1.61/0.56    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) | r2_hidden(sK3,X0)) )),
% 1.61/0.56    inference(resolution,[],[f196,f60])).
% 1.61/0.56  fof(f60,plain,(
% 1.61/0.56    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.61/0.56    inference(definition_unfolding,[],[f31,f41,f58])).
% 1.61/0.56  fof(f58,plain,(
% 1.61/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.61/0.56    inference(definition_unfolding,[],[f36,f57])).
% 1.61/0.56  fof(f57,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.61/0.56    inference(definition_unfolding,[],[f40,f52])).
% 1.61/0.56  fof(f52,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f14])).
% 1.61/0.56  fof(f14,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.61/0.56  fof(f40,plain,(
% 1.61/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f13])).
% 1.61/0.56  fof(f13,axiom,(
% 1.61/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.61/0.56  fof(f36,plain,(
% 1.61/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f12])).
% 1.61/0.56  fof(f12,axiom,(
% 1.61/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.61/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.61/0.56  fof(f31,plain,(
% 1.61/0.56    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.61/0.56    inference(cnf_transformation,[],[f25])).
% 1.61/0.58  fof(f196,plain,(
% 1.61/0.58    ( ! [X12,X10,X11] : (~r1_tarski(X12,k2_enumset1(X11,X11,X11,X11)) | r1_xboole_0(X12,X10) | r2_hidden(X11,X10)) )),
% 1.61/0.58    inference(superposition,[],[f56,f64])).
% 1.61/0.58  fof(f64,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f51,f58])).
% 1.61/0.58  fof(f51,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f30])).
% 1.61/0.58  fof(f30,plain,(
% 1.61/0.58    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.61/0.58    inference(nnf_transformation,[],[f15])).
% 1.61/0.58  fof(f15,axiom,(
% 1.61/0.58    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.61/0.58  fof(f2397,plain,(
% 1.61/0.58    spl5_42),
% 1.61/0.58    inference(avatar_contradiction_clause,[],[f2391])).
% 1.61/0.58  fof(f2391,plain,(
% 1.61/0.58    $false | spl5_42),
% 1.61/0.58    inference(resolution,[],[f2390,f33])).
% 1.61/0.58  fof(f2390,plain,(
% 1.61/0.58    ~r1_xboole_0(sK2,sK1) | spl5_42),
% 1.61/0.58    inference(resolution,[],[f2364,f439])).
% 1.61/0.58  fof(f2364,plain,(
% 1.61/0.58    ~r1_xboole_0(sK1,sK2) | spl5_42),
% 1.61/0.58    inference(avatar_component_clause,[],[f2362])).
% 1.61/0.58  % SZS output end Proof for theBenchmark
% 1.61/0.58  % (29096)------------------------------
% 1.61/0.58  % (29096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (29096)Termination reason: Refutation
% 1.61/0.58  
% 1.61/0.58  % (29096)Memory used [KB]: 7419
% 1.61/0.58  % (29096)Time elapsed: 0.137 s
% 1.61/0.58  % (29096)------------------------------
% 1.61/0.58  % (29096)------------------------------
% 1.61/0.58  % (29091)Success in time 0.225 s
%------------------------------------------------------------------------------
