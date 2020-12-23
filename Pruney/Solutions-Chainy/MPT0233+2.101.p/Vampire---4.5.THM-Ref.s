%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:17 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  170 (1302 expanded)
%              Number of leaves         :   32 ( 428 expanded)
%              Depth                    :   16
%              Number of atoms          :  508 (3528 expanded)
%              Number of equality atoms :  267 (2703 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f965,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f203,f231,f240,f358,f396,f436,f515,f585,f593,f595,f598,f687,f693,f716,f754,f760,f963])).

fof(f963,plain,
    ( ~ spl7_33
    | spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f962,f127,f168,f580])).

fof(f580,plain,
    ( spl7_33
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f168,plain,
    ( spl7_7
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f127,plain,
    ( spl7_2
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f962,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f958,f945])).

fof(f945,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f920,f935])).

fof(f935,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f928,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f928,plain,
    ( k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_2 ),
    inference(superposition,[],[f88,f920])).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f920,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f597,f128])).

fof(f128,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f597,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(resolution,[],[f89,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f61,f58])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f89,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f46,f86,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f958,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,k1_xboole_0))
        | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) )
    | ~ spl7_2 ),
    inference(superposition,[],[f92,f945])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f760,plain,
    ( spl7_34
    | spl7_2
    | spl7_3
    | spl7_25
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f758,f235,f363,f130,f127,f604])).

fof(f604,plain,
    ( spl7_34
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f130,plain,
    ( spl7_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f363,plain,
    ( spl7_25
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f235,plain,
    ( spl7_15
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f758,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)
    | ~ spl7_15 ),
    inference(resolution,[],[f599,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f64,f86,f87,f87,f86])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f86])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f599,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1))
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f89,f236])).

fof(f236,plain,
    ( sK1 = sK3
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f235])).

fof(f754,plain,
    ( ~ spl7_4
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f600,f738])).

fof(f738,plain,
    ( sK0 = sK1
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(resolution,[],[f637,f117])).

fof(f117,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f73,f85])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK6(X0,X1,X2,X3) != X2
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X2
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X0
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK6(X0,X1,X2,X3) != X2
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X2
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X0
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f637,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X6 )
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f632])).

fof(f632,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X6
        | sK1 = X6
        | sK1 = X6 )
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(superposition,[],[f120,f623])).

fof(f623,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f134,f236])).

fof(f134,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_4
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f120,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f71,f85])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f600,plain,
    ( sK0 != sK1
    | ~ spl7_15 ),
    inference(superposition,[],[f48,f236])).

fof(f48,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f716,plain,
    ( spl7_13
    | spl7_14
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f715,f604,f229,f226])).

fof(f226,plain,
    ( spl7_13
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f229,plain,
    ( spl7_14
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f715,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl7_34 ),
    inference(duplicate_literal_removal,[],[f714])).

fof(f714,plain,
    ( sK0 = sK2
    | sK0 = sK2
    | sK1 = sK2
    | ~ spl7_34 ),
    inference(resolution,[],[f704,f120])).

fof(f704,plain,
    ( r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_34 ),
    inference(superposition,[],[f119,f605])).

fof(f605,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f604])).

fof(f119,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f72,f85])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f693,plain,(
    ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f47,f230])).

fof(f230,plain,
    ( sK0 = sK2
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f229])).

fof(f47,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f687,plain,
    ( spl7_13
    | spl7_14
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f686,f130,f229,f226])).

fof(f686,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f685])).

fof(f685,plain,
    ( sK0 = sK2
    | sK0 = sK2
    | sK1 = sK2
    | ~ spl7_3 ),
    inference(resolution,[],[f616,f120])).

fof(f616,plain,
    ( r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_3 ),
    inference(superposition,[],[f119,f131])).

fof(f131,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f598,plain,
    ( spl7_1
    | spl7_2
    | spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f596,f133,f130,f127,f124])).

fof(f124,plain,
    ( spl7_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f596,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(resolution,[],[f89,f100])).

fof(f595,plain,(
    ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f48,f239])).

fof(f239,plain,
    ( sK0 = sK3
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl7_16
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f593,plain,
    ( spl7_2
    | spl7_25
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f592,f235,f226,f363,f127])).

fof(f592,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f590])).

fof(f590,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(resolution,[],[f589,f100])).

fof(f589,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f316,f236])).

fof(f316,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3))
    | ~ spl7_13 ),
    inference(backward_demodulation,[],[f89,f227])).

fof(f227,plain,
    ( sK1 = sK2
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f226])).

fof(f585,plain,(
    spl7_33 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | spl7_33 ),
    inference(resolution,[],[f581,f49])).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f581,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl7_33 ),
    inference(avatar_component_clause,[],[f580])).

fof(f515,plain,
    ( spl7_24
    | spl7_2
    | spl7_25
    | spl7_4
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f440,f226,f133,f363,f127,f360])).

fof(f360,plain,
    ( spl7_24
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f440,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f316,f100])).

fof(f436,plain,
    ( spl7_15
    | spl7_16
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f435,f360,f238,f235])).

fof(f435,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f434])).

fof(f434,plain,
    ( sK0 = sK3
    | sK0 = sK3
    | sK1 = sK3
    | ~ spl7_24 ),
    inference(resolution,[],[f410,f120])).

fof(f410,plain,
    ( r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_24 ),
    inference(superposition,[],[f115,f361])).

fof(f361,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f360])).

fof(f115,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f74,f85])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f396,plain,
    ( ~ spl7_13
    | ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | ~ spl7_13
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f243,f384])).

fof(f384,plain,
    ( sK0 = sK1
    | ~ spl7_25 ),
    inference(resolution,[],[f380,f117])).

fof(f380,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X6 )
    | ~ spl7_25 ),
    inference(duplicate_literal_removal,[],[f375])).

fof(f375,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X6
        | sK1 = X6
        | sK1 = X6 )
    | ~ spl7_25 ),
    inference(superposition,[],[f120,f364])).

fof(f364,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f363])).

fof(f243,plain,
    ( sK0 != sK1
    | ~ spl7_13 ),
    inference(superposition,[],[f47,f227])).

fof(f358,plain,
    ( spl7_15
    | spl7_16
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f357,f133,f238,f235])).

fof(f357,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f356])).

fof(f356,plain,
    ( sK0 = sK3
    | sK0 = sK3
    | sK1 = sK3
    | ~ spl7_4 ),
    inference(resolution,[],[f309,f120])).

fof(f309,plain,
    ( r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_4 ),
    inference(superposition,[],[f119,f134])).

fof(f240,plain,
    ( spl7_15
    | spl7_16
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f233,f124,f238,f235])).

fof(f233,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl7_1 ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,
    ( sK0 = sK3
    | sK0 = sK3
    | sK1 = sK3
    | ~ spl7_1 ),
    inference(resolution,[],[f217,f120])).

fof(f217,plain,
    ( r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_1 ),
    inference(superposition,[],[f115,f125])).

fof(f125,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f231,plain,
    ( spl7_13
    | spl7_14
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f224,f124,f229,f226])).

fof(f224,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl7_1 ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( sK0 = sK2
    | sK0 = sK2
    | sK1 = sK2
    | ~ spl7_1 ),
    inference(resolution,[],[f215,f120])).

fof(f215,plain,
    ( r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_1 ),
    inference(superposition,[],[f119,f125])).

fof(f203,plain,
    ( ~ spl7_2
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f145,f169])).

fof(f169,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f168])).

fof(f145,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_2 ),
    inference(superposition,[],[f115,f128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:35:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (21059)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.50  % (21067)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (21079)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (21082)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (21065)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (21071)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (21066)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (21056)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (21066)Refutation not found, incomplete strategy% (21066)------------------------------
% 0.22/0.52  % (21066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21066)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21066)Memory used [KB]: 10618
% 0.22/0.52  % (21066)Time elapsed: 0.108 s
% 0.22/0.52  % (21066)------------------------------
% 0.22/0.52  % (21066)------------------------------
% 0.22/0.52  % (21069)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (21056)Refutation not found, incomplete strategy% (21056)------------------------------
% 0.22/0.52  % (21056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21056)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21056)Memory used [KB]: 1663
% 0.22/0.52  % (21056)Time elapsed: 0.106 s
% 0.22/0.52  % (21056)------------------------------
% 0.22/0.52  % (21056)------------------------------
% 0.22/0.52  % (21078)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (21065)Refutation not found, incomplete strategy% (21065)------------------------------
% 0.22/0.52  % (21065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21065)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21065)Memory used [KB]: 10618
% 0.22/0.52  % (21065)Time elapsed: 0.119 s
% 0.22/0.52  % (21065)------------------------------
% 0.22/0.52  % (21065)------------------------------
% 0.22/0.52  % (21057)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (21060)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (21058)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (21062)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (21068)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (21073)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (21083)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (21073)Refutation not found, incomplete strategy% (21073)------------------------------
% 0.22/0.53  % (21073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21073)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21073)Memory used [KB]: 10618
% 0.22/0.53  % (21073)Time elapsed: 0.129 s
% 0.22/0.53  % (21073)------------------------------
% 0.22/0.53  % (21073)------------------------------
% 0.22/0.53  % (21077)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (21071)Refutation not found, incomplete strategy% (21071)------------------------------
% 0.22/0.53  % (21071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21070)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (21061)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (21071)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21071)Memory used [KB]: 6268
% 0.22/0.53  % (21071)Time elapsed: 0.124 s
% 0.22/0.53  % (21071)------------------------------
% 0.22/0.53  % (21071)------------------------------
% 0.22/0.54  % (21080)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (21075)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (21081)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (21084)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (21076)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (21064)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.55  % (21072)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.55  % (21074)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.55  % (21085)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.56  % (21063)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.57/0.57  % (21058)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.57  % SZS output start Proof for theBenchmark
% 1.57/0.57  fof(f965,plain,(
% 1.57/0.57    $false),
% 1.57/0.57    inference(avatar_sat_refutation,[],[f203,f231,f240,f358,f396,f436,f515,f585,f593,f595,f598,f687,f693,f716,f754,f760,f963])).
% 1.57/0.57  fof(f963,plain,(
% 1.57/0.57    ~spl7_33 | spl7_7 | ~spl7_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f962,f127,f168,f580])).
% 1.57/0.59  fof(f580,plain,(
% 1.57/0.59    spl7_33 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 1.57/0.59  fof(f168,plain,(
% 1.57/0.59    spl7_7 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.57/0.59  fof(f127,plain,(
% 1.57/0.59    spl7_2 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.57/0.59  fof(f962,plain,(
% 1.57/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)) ) | ~spl7_2),
% 1.57/0.59    inference(forward_demodulation,[],[f958,f945])).
% 1.57/0.59  fof(f945,plain,(
% 1.57/0.59    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl7_2),
% 1.57/0.59    inference(backward_demodulation,[],[f920,f935])).
% 1.57/0.59  fof(f935,plain,(
% 1.57/0.59    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl7_2),
% 1.57/0.59    inference(forward_demodulation,[],[f928,f50])).
% 1.57/0.59  fof(f50,plain,(
% 1.57/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.59    inference(cnf_transformation,[],[f9])).
% 1.57/0.59  fof(f9,axiom,(
% 1.57/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.57/0.59  fof(f928,plain,(
% 1.57/0.59    k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl7_2),
% 1.57/0.59    inference(superposition,[],[f88,f920])).
% 1.57/0.59  fof(f88,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.57/0.59    inference(definition_unfolding,[],[f57,f58])).
% 1.57/0.59  fof(f58,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f8])).
% 1.57/0.59  fof(f8,axiom,(
% 1.57/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.57/0.59  fof(f57,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f5])).
% 1.57/0.59  fof(f5,axiom,(
% 1.57/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.59  fof(f920,plain,(
% 1.57/0.59    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) | ~spl7_2),
% 1.57/0.59    inference(forward_demodulation,[],[f597,f128])).
% 1.57/0.59  fof(f128,plain,(
% 1.57/0.59    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl7_2),
% 1.57/0.59    inference(avatar_component_clause,[],[f127])).
% 1.57/0.59  fof(f597,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))),
% 1.57/0.59    inference(resolution,[],[f89,f94])).
% 1.57/0.59  fof(f94,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.57/0.59    inference(definition_unfolding,[],[f61,f58])).
% 1.57/0.59  fof(f61,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f29])).
% 1.57/0.59  fof(f29,plain,(
% 1.57/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.57/0.59    inference(ennf_transformation,[],[f7])).
% 1.57/0.59  fof(f7,axiom,(
% 1.57/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.57/0.59  fof(f89,plain,(
% 1.57/0.59    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.57/0.59    inference(definition_unfolding,[],[f46,f86,f86])).
% 1.57/0.59  fof(f86,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f55,f85])).
% 1.57/0.59  fof(f85,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f62,f84])).
% 1.57/0.59  fof(f84,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f69,f83])).
% 1.57/0.59  fof(f83,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f79,f82])).
% 1.57/0.59  fof(f82,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f80,f81])).
% 1.57/0.59  fof(f81,plain,(
% 1.57/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f20])).
% 1.57/0.59  fof(f20,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.57/0.59  fof(f80,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f19])).
% 1.57/0.59  fof(f19,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.57/0.59  fof(f79,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f18])).
% 1.57/0.59  fof(f18,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.57/0.59  fof(f69,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f17])).
% 1.57/0.59  fof(f17,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.57/0.59  fof(f62,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f16])).
% 1.57/0.59  fof(f16,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.57/0.59  fof(f55,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f15])).
% 1.57/0.59  fof(f15,axiom,(
% 1.57/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.57/0.59  fof(f46,plain,(
% 1.57/0.59    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.57/0.59    inference(cnf_transformation,[],[f34])).
% 1.57/0.59  fof(f34,plain,(
% 1.57/0.59    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f33])).
% 1.57/0.59  fof(f33,plain,(
% 1.57/0.59    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f26,plain,(
% 1.57/0.59    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.57/0.59    inference(ennf_transformation,[],[f23])).
% 1.57/0.59  fof(f23,negated_conjecture,(
% 1.57/0.59    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.57/0.59    inference(negated_conjecture,[],[f22])).
% 1.57/0.59  fof(f22,conjecture,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.57/0.59  fof(f958,plain,(
% 1.57/0.59    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)) ) | ~spl7_2),
% 1.57/0.59    inference(superposition,[],[f92,f945])).
% 1.57/0.59  fof(f92,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f60,f58])).
% 1.57/0.59  fof(f60,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f38])).
% 1.57/0.59  fof(f38,plain,(
% 1.57/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f37])).
% 1.57/0.59  fof(f37,plain,(
% 1.57/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f28,plain,(
% 1.57/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.59    inference(ennf_transformation,[],[f25])).
% 1.57/0.59  fof(f25,plain,(
% 1.57/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.59    inference(rectify,[],[f3])).
% 1.57/0.59  fof(f3,axiom,(
% 1.57/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.57/0.59  fof(f760,plain,(
% 1.57/0.59    spl7_34 | spl7_2 | spl7_3 | spl7_25 | ~spl7_15),
% 1.57/0.59    inference(avatar_split_clause,[],[f758,f235,f363,f130,f127,f604])).
% 1.57/0.59  fof(f604,plain,(
% 1.57/0.59    spl7_34 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 1.57/0.59  fof(f130,plain,(
% 1.57/0.59    spl7_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.57/0.59  fof(f363,plain,(
% 1.57/0.59    spl7_25 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.57/0.59  fof(f235,plain,(
% 1.57/0.59    spl7_15 <=> sK1 = sK3),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.57/0.59  fof(f758,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1) | ~spl7_15),
% 1.57/0.59    inference(resolution,[],[f599,f100])).
% 1.57/0.59  fof(f100,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0) )),
% 1.57/0.59    inference(definition_unfolding,[],[f64,f86,f87,f87,f86])).
% 1.57/0.59  fof(f87,plain,(
% 1.57/0.59    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.57/0.59    inference(definition_unfolding,[],[f51,f86])).
% 1.57/0.59  fof(f51,plain,(
% 1.57/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f14])).
% 1.57/0.59  fof(f14,axiom,(
% 1.57/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.57/0.59  fof(f64,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f40])).
% 1.57/0.59  fof(f40,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.57/0.59    inference(flattening,[],[f39])).
% 1.57/0.59  fof(f39,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.57/0.59    inference(nnf_transformation,[],[f31])).
% 1.57/0.59  fof(f31,plain,(
% 1.57/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f21])).
% 1.57/0.59  fof(f21,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.57/0.59  fof(f599,plain,(
% 1.57/0.59    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)) | ~spl7_15),
% 1.57/0.59    inference(backward_demodulation,[],[f89,f236])).
% 1.57/0.59  fof(f236,plain,(
% 1.57/0.59    sK1 = sK3 | ~spl7_15),
% 1.57/0.59    inference(avatar_component_clause,[],[f235])).
% 1.57/0.59  fof(f754,plain,(
% 1.57/0.59    ~spl7_4 | ~spl7_15),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f743])).
% 1.57/0.59  fof(f743,plain,(
% 1.57/0.59    $false | (~spl7_4 | ~spl7_15)),
% 1.57/0.59    inference(subsumption_resolution,[],[f600,f738])).
% 1.57/0.59  fof(f738,plain,(
% 1.57/0.59    sK0 = sK1 | (~spl7_4 | ~spl7_15)),
% 1.57/0.59    inference(resolution,[],[f637,f117])).
% 1.57/0.59  fof(f117,plain,(
% 1.57/0.59    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 1.57/0.59    inference(equality_resolution,[],[f116])).
% 1.57/0.59  fof(f116,plain,(
% 1.57/0.59    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 1.57/0.59    inference(equality_resolution,[],[f107])).
% 1.57/0.59  fof(f107,plain,(
% 1.57/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.57/0.59    inference(definition_unfolding,[],[f73,f85])).
% 1.57/0.59  fof(f73,plain,(
% 1.57/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.57/0.59    inference(cnf_transformation,[],[f45])).
% 1.57/0.59  fof(f45,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK6(X0,X1,X2,X3) != X2 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X2 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X0 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.57/0.59  fof(f44,plain,(
% 1.57/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X2 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X2 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X0 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f43,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.59    inference(rectify,[],[f42])).
% 1.57/0.59  fof(f42,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.59    inference(flattening,[],[f41])).
% 1.57/0.59  fof(f41,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.59    inference(nnf_transformation,[],[f32])).
% 1.57/0.59  fof(f32,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.57/0.59    inference(ennf_transformation,[],[f12])).
% 1.57/0.59  fof(f12,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.57/0.59  fof(f637,plain,(
% 1.57/0.59    ( ! [X6] : (~r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X6) ) | (~spl7_4 | ~spl7_15)),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f632])).
% 1.57/0.59  fof(f632,plain,(
% 1.57/0.59    ( ! [X6] : (~r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X6 | sK1 = X6 | sK1 = X6) ) | (~spl7_4 | ~spl7_15)),
% 1.57/0.59    inference(superposition,[],[f120,f623])).
% 1.57/0.59  fof(f623,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | (~spl7_4 | ~spl7_15)),
% 1.57/0.59    inference(forward_demodulation,[],[f134,f236])).
% 1.57/0.59  fof(f134,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~spl7_4),
% 1.57/0.59    inference(avatar_component_clause,[],[f133])).
% 1.57/0.59  fof(f133,plain,(
% 1.57/0.59    spl7_4 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.57/0.59  fof(f120,plain,(
% 1.57/0.59    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.57/0.59    inference(equality_resolution,[],[f109])).
% 1.57/0.59  fof(f109,plain,(
% 1.57/0.59    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.57/0.59    inference(definition_unfolding,[],[f71,f85])).
% 1.57/0.59  fof(f71,plain,(
% 1.57/0.59    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.57/0.59    inference(cnf_transformation,[],[f45])).
% 1.57/0.59  fof(f600,plain,(
% 1.57/0.59    sK0 != sK1 | ~spl7_15),
% 1.57/0.59    inference(superposition,[],[f48,f236])).
% 1.57/0.59  fof(f48,plain,(
% 1.57/0.59    sK0 != sK3),
% 1.57/0.59    inference(cnf_transformation,[],[f34])).
% 1.57/0.59  fof(f716,plain,(
% 1.57/0.59    spl7_13 | spl7_14 | ~spl7_34),
% 1.57/0.59    inference(avatar_split_clause,[],[f715,f604,f229,f226])).
% 1.57/0.59  fof(f226,plain,(
% 1.57/0.59    spl7_13 <=> sK1 = sK2),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.57/0.59  fof(f229,plain,(
% 1.57/0.59    spl7_14 <=> sK0 = sK2),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.57/0.59  fof(f715,plain,(
% 1.57/0.59    sK0 = sK2 | sK1 = sK2 | ~spl7_34),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f714])).
% 1.57/0.59  fof(f714,plain,(
% 1.57/0.59    sK0 = sK2 | sK0 = sK2 | sK1 = sK2 | ~spl7_34),
% 1.57/0.59    inference(resolution,[],[f704,f120])).
% 1.57/0.59  fof(f704,plain,(
% 1.57/0.59    r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_34),
% 1.57/0.59    inference(superposition,[],[f119,f605])).
% 1.57/0.59  fof(f605,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1) | ~spl7_34),
% 1.57/0.59    inference(avatar_component_clause,[],[f604])).
% 1.57/0.59  fof(f119,plain,(
% 1.57/0.59    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 1.57/0.59    inference(equality_resolution,[],[f118])).
% 1.57/0.59  fof(f118,plain,(
% 1.57/0.59    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 1.57/0.59    inference(equality_resolution,[],[f108])).
% 1.57/0.59  fof(f108,plain,(
% 1.57/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.57/0.59    inference(definition_unfolding,[],[f72,f85])).
% 1.57/0.59  fof(f72,plain,(
% 1.57/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.57/0.59    inference(cnf_transformation,[],[f45])).
% 1.57/0.59  fof(f693,plain,(
% 1.57/0.59    ~spl7_14),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f688])).
% 1.57/0.59  fof(f688,plain,(
% 1.57/0.59    $false | ~spl7_14),
% 1.57/0.59    inference(subsumption_resolution,[],[f47,f230])).
% 1.57/0.59  fof(f230,plain,(
% 1.57/0.59    sK0 = sK2 | ~spl7_14),
% 1.57/0.59    inference(avatar_component_clause,[],[f229])).
% 1.57/0.59  fof(f47,plain,(
% 1.57/0.59    sK0 != sK2),
% 1.57/0.59    inference(cnf_transformation,[],[f34])).
% 1.57/0.59  fof(f687,plain,(
% 1.57/0.59    spl7_13 | spl7_14 | ~spl7_3),
% 1.57/0.59    inference(avatar_split_clause,[],[f686,f130,f229,f226])).
% 1.57/0.59  fof(f686,plain,(
% 1.57/0.59    sK0 = sK2 | sK1 = sK2 | ~spl7_3),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f685])).
% 1.57/0.59  fof(f685,plain,(
% 1.57/0.59    sK0 = sK2 | sK0 = sK2 | sK1 = sK2 | ~spl7_3),
% 1.57/0.59    inference(resolution,[],[f616,f120])).
% 1.57/0.59  fof(f616,plain,(
% 1.57/0.59    r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_3),
% 1.57/0.59    inference(superposition,[],[f119,f131])).
% 1.57/0.59  fof(f131,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl7_3),
% 1.57/0.59    inference(avatar_component_clause,[],[f130])).
% 1.57/0.59  fof(f598,plain,(
% 1.57/0.59    spl7_1 | spl7_2 | spl7_3 | spl7_4),
% 1.57/0.59    inference(avatar_split_clause,[],[f596,f133,f130,f127,f124])).
% 1.57/0.59  fof(f124,plain,(
% 1.57/0.59    spl7_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.57/0.59  fof(f596,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 1.57/0.59    inference(resolution,[],[f89,f100])).
% 1.57/0.59  fof(f595,plain,(
% 1.57/0.59    ~spl7_16),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f594])).
% 1.57/0.59  fof(f594,plain,(
% 1.57/0.59    $false | ~spl7_16),
% 1.57/0.59    inference(subsumption_resolution,[],[f48,f239])).
% 1.57/0.59  fof(f239,plain,(
% 1.57/0.59    sK0 = sK3 | ~spl7_16),
% 1.57/0.59    inference(avatar_component_clause,[],[f238])).
% 1.57/0.59  fof(f238,plain,(
% 1.57/0.59    spl7_16 <=> sK0 = sK3),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.57/0.59  fof(f593,plain,(
% 1.57/0.59    spl7_2 | spl7_25 | ~spl7_13 | ~spl7_15),
% 1.57/0.59    inference(avatar_split_clause,[],[f592,f235,f226,f363,f127])).
% 1.57/0.59  fof(f592,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | (~spl7_13 | ~spl7_15)),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f590])).
% 1.57/0.59  fof(f590,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | (~spl7_13 | ~spl7_15)),
% 1.57/0.59    inference(resolution,[],[f589,f100])).
% 1.57/0.59  fof(f589,plain,(
% 1.57/0.59    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | (~spl7_13 | ~spl7_15)),
% 1.57/0.59    inference(forward_demodulation,[],[f316,f236])).
% 1.57/0.59  fof(f316,plain,(
% 1.57/0.59    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3)) | ~spl7_13),
% 1.57/0.59    inference(backward_demodulation,[],[f89,f227])).
% 1.57/0.59  fof(f227,plain,(
% 1.57/0.59    sK1 = sK2 | ~spl7_13),
% 1.57/0.59    inference(avatar_component_clause,[],[f226])).
% 1.57/0.59  fof(f585,plain,(
% 1.57/0.59    spl7_33),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f584])).
% 1.57/0.59  fof(f584,plain,(
% 1.57/0.59    $false | spl7_33),
% 1.57/0.59    inference(resolution,[],[f581,f49])).
% 1.57/0.59  fof(f49,plain,(
% 1.57/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f10])).
% 1.57/0.59  fof(f10,axiom,(
% 1.57/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.57/0.59  fof(f581,plain,(
% 1.57/0.59    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl7_33),
% 1.57/0.59    inference(avatar_component_clause,[],[f580])).
% 1.57/0.59  fof(f515,plain,(
% 1.57/0.59    spl7_24 | spl7_2 | spl7_25 | spl7_4 | ~spl7_13),
% 1.57/0.59    inference(avatar_split_clause,[],[f440,f226,f133,f363,f127,f360])).
% 1.57/0.59  fof(f360,plain,(
% 1.57/0.59    spl7_24 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.57/0.59  fof(f440,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3) | ~spl7_13),
% 1.57/0.59    inference(resolution,[],[f316,f100])).
% 1.57/0.59  fof(f436,plain,(
% 1.57/0.59    spl7_15 | spl7_16 | ~spl7_24),
% 1.57/0.59    inference(avatar_split_clause,[],[f435,f360,f238,f235])).
% 1.57/0.59  fof(f435,plain,(
% 1.57/0.59    sK0 = sK3 | sK1 = sK3 | ~spl7_24),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f434])).
% 1.57/0.59  fof(f434,plain,(
% 1.57/0.59    sK0 = sK3 | sK0 = sK3 | sK1 = sK3 | ~spl7_24),
% 1.57/0.59    inference(resolution,[],[f410,f120])).
% 1.57/0.59  fof(f410,plain,(
% 1.57/0.59    r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_24),
% 1.57/0.59    inference(superposition,[],[f115,f361])).
% 1.57/0.59  fof(f361,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3) | ~spl7_24),
% 1.57/0.59    inference(avatar_component_clause,[],[f360])).
% 1.57/0.59  fof(f115,plain,(
% 1.57/0.59    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 1.57/0.59    inference(equality_resolution,[],[f114])).
% 1.57/0.59  fof(f114,plain,(
% 1.57/0.59    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 1.57/0.59    inference(equality_resolution,[],[f106])).
% 1.57/0.59  fof(f106,plain,(
% 1.57/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.57/0.59    inference(definition_unfolding,[],[f74,f85])).
% 1.57/0.59  fof(f74,plain,(
% 1.57/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.57/0.59    inference(cnf_transformation,[],[f45])).
% 1.57/0.59  fof(f396,plain,(
% 1.57/0.59    ~spl7_13 | ~spl7_25),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f389])).
% 1.57/0.59  fof(f389,plain,(
% 1.57/0.59    $false | (~spl7_13 | ~spl7_25)),
% 1.57/0.59    inference(subsumption_resolution,[],[f243,f384])).
% 1.57/0.59  fof(f384,plain,(
% 1.57/0.59    sK0 = sK1 | ~spl7_25),
% 1.57/0.59    inference(resolution,[],[f380,f117])).
% 1.57/0.59  fof(f380,plain,(
% 1.57/0.59    ( ! [X6] : (~r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X6) ) | ~spl7_25),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f375])).
% 1.57/0.59  fof(f375,plain,(
% 1.57/0.59    ( ! [X6] : (~r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X6 | sK1 = X6 | sK1 = X6) ) | ~spl7_25),
% 1.57/0.59    inference(superposition,[],[f120,f364])).
% 1.57/0.59  fof(f364,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl7_25),
% 1.57/0.59    inference(avatar_component_clause,[],[f363])).
% 1.57/0.59  fof(f243,plain,(
% 1.57/0.59    sK0 != sK1 | ~spl7_13),
% 1.57/0.59    inference(superposition,[],[f47,f227])).
% 1.57/0.59  fof(f358,plain,(
% 1.57/0.59    spl7_15 | spl7_16 | ~spl7_4),
% 1.57/0.59    inference(avatar_split_clause,[],[f357,f133,f238,f235])).
% 1.57/0.59  fof(f357,plain,(
% 1.57/0.59    sK0 = sK3 | sK1 = sK3 | ~spl7_4),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f356])).
% 1.57/0.59  fof(f356,plain,(
% 1.57/0.59    sK0 = sK3 | sK0 = sK3 | sK1 = sK3 | ~spl7_4),
% 1.57/0.59    inference(resolution,[],[f309,f120])).
% 1.57/0.59  fof(f309,plain,(
% 1.57/0.59    r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_4),
% 1.57/0.59    inference(superposition,[],[f119,f134])).
% 1.57/0.59  fof(f240,plain,(
% 1.57/0.59    spl7_15 | spl7_16 | ~spl7_1),
% 1.57/0.59    inference(avatar_split_clause,[],[f233,f124,f238,f235])).
% 1.57/0.59  fof(f233,plain,(
% 1.57/0.59    sK0 = sK3 | sK1 = sK3 | ~spl7_1),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f232])).
% 1.57/0.59  fof(f232,plain,(
% 1.57/0.59    sK0 = sK3 | sK0 = sK3 | sK1 = sK3 | ~spl7_1),
% 1.57/0.59    inference(resolution,[],[f217,f120])).
% 1.57/0.59  fof(f217,plain,(
% 1.57/0.59    r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_1),
% 1.57/0.59    inference(superposition,[],[f115,f125])).
% 1.57/0.59  fof(f125,plain,(
% 1.57/0.59    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) | ~spl7_1),
% 1.57/0.59    inference(avatar_component_clause,[],[f124])).
% 1.57/0.59  fof(f231,plain,(
% 1.57/0.59    spl7_13 | spl7_14 | ~spl7_1),
% 1.57/0.59    inference(avatar_split_clause,[],[f224,f124,f229,f226])).
% 1.57/0.59  fof(f224,plain,(
% 1.57/0.59    sK0 = sK2 | sK1 = sK2 | ~spl7_1),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f223])).
% 1.57/0.59  fof(f223,plain,(
% 1.57/0.59    sK0 = sK2 | sK0 = sK2 | sK1 = sK2 | ~spl7_1),
% 1.57/0.59    inference(resolution,[],[f215,f120])).
% 1.57/0.59  fof(f215,plain,(
% 1.57/0.59    r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_1),
% 1.57/0.59    inference(superposition,[],[f119,f125])).
% 1.57/0.59  fof(f203,plain,(
% 1.57/0.59    ~spl7_2 | ~spl7_7),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f199])).
% 1.57/0.59  fof(f199,plain,(
% 1.57/0.59    $false | (~spl7_2 | ~spl7_7)),
% 1.57/0.59    inference(subsumption_resolution,[],[f145,f169])).
% 1.57/0.59  fof(f169,plain,(
% 1.57/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl7_7),
% 1.57/0.59    inference(avatar_component_clause,[],[f168])).
% 1.57/0.59  fof(f145,plain,(
% 1.57/0.59    r2_hidden(sK1,k1_xboole_0) | ~spl7_2),
% 1.57/0.59    inference(superposition,[],[f115,f128])).
% 1.57/0.59  % SZS output end Proof for theBenchmark
% 1.57/0.59  % (21058)------------------------------
% 1.57/0.59  % (21058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (21058)Termination reason: Refutation
% 1.57/0.59  
% 1.57/0.59  % (21058)Memory used [KB]: 11129
% 1.57/0.59  % (21058)Time elapsed: 0.158 s
% 1.57/0.59  % (21058)------------------------------
% 1.57/0.59  % (21058)------------------------------
% 1.57/0.59  % (21055)Success in time 0.232 s
%------------------------------------------------------------------------------
