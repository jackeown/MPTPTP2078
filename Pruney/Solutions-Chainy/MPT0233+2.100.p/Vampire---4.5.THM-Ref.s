%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 937 expanded)
%              Number of leaves         :   31 ( 300 expanded)
%              Depth                    :   16
%              Number of atoms          :  481 (2826 expanded)
%              Number of equality atoms :  252 (2126 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f886,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f190,f234,f253,f257,f317,f395,f419,f422,f495,f535,f622,f626,f855,f885])).

fof(f885,plain,
    ( ~ spl7_2
    | spl7_8 ),
    inference(avatar_contradiction_clause,[],[f884])).

% (463)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f884,plain,
    ( $false
    | ~ spl7_2
    | spl7_8 ),
    inference(resolution,[],[f874,f49])).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f874,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_2
    | spl7_8 ),
    inference(backward_demodulation,[],[f182,f872])).

fof(f872,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f844,f856])).

fof(f856,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f848,f50])).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f848,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl7_2 ),
    inference(superposition,[],[f88,f837])).

fof(f837,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f421,f128])).

fof(f128,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_2
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f421,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(resolution,[],[f89,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f61,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

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

% (464)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f844,plain,
    ( k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_2 ),
    inference(superposition,[],[f88,f837])).

fof(f182,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_8
  <=> r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f855,plain,
    ( ~ spl7_8
    | spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f854,f127,f169,f175])).

fof(f169,plain,
    ( spl7_7
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f854,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f847,f50])).

% (466)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f847,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(k1_xboole_0,k1_xboole_0))
        | ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) )
    | ~ spl7_2 ),
    inference(superposition,[],[f92,f837])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f626,plain,
    ( spl7_29
    | spl7_2
    | spl7_23
    | spl7_4
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f624,f229,f133,f330,f127,f428])).

fof(f428,plain,
    ( spl7_29
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f330,plain,
    ( spl7_23
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f133,plain,
    ( spl7_4
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f229,plain,
    ( spl7_12
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f624,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3)
    | ~ spl7_12 ),
    inference(resolution,[],[f423,f100])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f423,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3))
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f89,f230])).

fof(f230,plain,
    ( sK1 = sK2
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f229])).

fof(f622,plain,
    ( ~ spl7_12
    | ~ spl7_20
    | ~ spl7_29 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f424,f611])).

fof(f611,plain,
    ( sK0 = sK1
    | ~ spl7_20
    | ~ spl7_29 ),
    inference(resolution,[],[f598,f117])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f598,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X6 )
    | ~ spl7_20
    | ~ spl7_29 ),
    inference(duplicate_literal_removal,[],[f593])).

fof(f593,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X6
        | sK1 = X6
        | sK1 = X6 )
    | ~ spl7_20
    | ~ spl7_29 ),
    inference(superposition,[],[f120,f537])).

fof(f537,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_20
    | ~ spl7_29 ),
    inference(backward_demodulation,[],[f429,f313])).

fof(f313,plain,
    ( sK1 = sK3
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl7_20
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f429,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f428])).

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

% (460)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f424,plain,
    ( sK0 != sK1
    | ~ spl7_12 ),
    inference(superposition,[],[f47,f230])).

fof(f47,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f535,plain,
    ( spl7_20
    | spl7_21
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f534,f428,f315,f312])).

fof(f315,plain,
    ( spl7_21
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f534,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl7_29 ),
    inference(duplicate_literal_removal,[],[f533])).

fof(f533,plain,
    ( sK0 = sK3
    | sK0 = sK3
    | sK1 = sK3
    | ~ spl7_29 ),
    inference(resolution,[],[f509,f120])).

fof(f509,plain,
    ( r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_29 ),
    inference(superposition,[],[f115,f429])).

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

fof(f495,plain,
    ( ~ spl7_12
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f424,f481])).

fof(f481,plain,
    ( sK0 = sK1
    | ~ spl7_23 ),
    inference(resolution,[],[f445,f117])).

fof(f445,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X6 )
    | ~ spl7_23 ),
    inference(duplicate_literal_removal,[],[f440])).

fof(f440,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X6
        | sK1 = X6
        | sK1 = X6 )
    | ~ spl7_23 ),
    inference(superposition,[],[f120,f331])).

fof(f331,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f330])).

fof(f422,plain,
    ( spl7_1
    | spl7_2
    | spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f420,f133,f130,f127,f124])).

fof(f124,plain,
    ( spl7_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f130,plain,
    ( spl7_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f420,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(resolution,[],[f89,f100])).

% (451)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (456)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (458)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (454)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (455)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (451)Refutation not found, incomplete strategy% (451)------------------------------
% (451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (449)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (471)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (451)Termination reason: Refutation not found, incomplete strategy

% (451)Memory used [KB]: 10618
% (451)Time elapsed: 0.149 s
% (451)------------------------------
% (451)------------------------------
fof(f419,plain,(
    ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f48,f316])).

fof(f316,plain,
    ( sK0 = sK3
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f315])).

fof(f48,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f395,plain,
    ( ~ spl7_4
    | ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f323,f380])).

fof(f380,plain,
    ( sK0 = sK1
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(resolution,[],[f346,f117])).

fof(f346,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X6 )
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(duplicate_literal_removal,[],[f341])).

fof(f341,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X6
        | sK1 = X6
        | sK1 = X6 )
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(superposition,[],[f120,f320])).

fof(f320,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(backward_demodulation,[],[f134,f313])).

fof(f134,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f323,plain,
    ( sK0 != sK1
    | ~ spl7_20 ),
    inference(superposition,[],[f48,f313])).

fof(f317,plain,
    ( spl7_20
    | spl7_21
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f310,f133,f315,f312])).

fof(f310,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,
    ( sK0 = sK3
    | sK0 = sK3
    | sK1 = sK3
    | ~ spl7_4 ),
    inference(resolution,[],[f270,f120])).

fof(f270,plain,
    ( r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_4 ),
    inference(superposition,[],[f119,f134])).

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

fof(f257,plain,(
    ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f47,f233])).

fof(f233,plain,
    ( sK0 = sK2
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl7_13
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f253,plain,
    ( spl7_12
    | spl7_13
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f252,f124,f232,f229])).

fof(f252,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl7_1 ),
    inference(duplicate_literal_removal,[],[f251])).

fof(f251,plain,
    ( sK0 = sK2
    | sK0 = sK2
    | sK1 = sK2
    | ~ spl7_1 ),
    inference(resolution,[],[f243,f120])).

fof(f243,plain,
    ( r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_1 ),
    inference(superposition,[],[f119,f125])).

fof(f125,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f234,plain,
    ( spl7_12
    | spl7_13
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f227,f130,f232,f229])).

fof(f227,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,
    ( sK0 = sK2
    | sK0 = sK2
    | sK1 = sK2
    | ~ spl7_3 ),
    inference(resolution,[],[f219,f120])).

fof(f219,plain,
    ( r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_3 ),
    inference(superposition,[],[f119,f131])).

fof(f131,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f190,plain,
    ( ~ spl7_2
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f145,f170])).

fof(f170,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f169])).

fof(f145,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_2 ),
    inference(superposition,[],[f115,f128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:04:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (440)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (440)Refutation not found, incomplete strategy% (440)------------------------------
% 0.21/0.52  % (440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (440)Memory used [KB]: 1663
% 0.21/0.52  % (440)Time elapsed: 0.091 s
% 0.21/0.52  % (440)------------------------------
% 0.21/0.52  % (440)------------------------------
% 0.21/0.53  % (442)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (448)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (445)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (461)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (469)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.58  % (462)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (446)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (443)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (441)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.58  % (465)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  % (447)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.59  % (442)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % (457)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.60  % (457)Refutation not found, incomplete strategy% (457)------------------------------
% 0.21/0.60  % (457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (457)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (457)Memory used [KB]: 6268
% 0.21/0.60  % (457)Time elapsed: 0.126 s
% 0.21/0.60  % (457)------------------------------
% 0.21/0.60  % (457)------------------------------
% 0.21/0.60  % (459)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.60  % (459)Refutation not found, incomplete strategy% (459)------------------------------
% 0.21/0.60  % (459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (459)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (459)Memory used [KB]: 10618
% 0.21/0.60  % (459)Time elapsed: 0.174 s
% 0.21/0.60  % (459)------------------------------
% 0.21/0.60  % (459)------------------------------
% 0.21/0.60  % (468)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.60  % (467)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f886,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(avatar_sat_refutation,[],[f190,f234,f253,f257,f317,f395,f419,f422,f495,f535,f622,f626,f855,f885])).
% 0.21/0.60  fof(f885,plain,(
% 0.21/0.60    ~spl7_2 | spl7_8),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f884])).
% 0.21/0.60  % (463)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.60  fof(f884,plain,(
% 0.21/0.60    $false | (~spl7_2 | spl7_8)),
% 0.21/0.60    inference(resolution,[],[f874,f49])).
% 0.21/0.60  fof(f49,plain,(
% 0.21/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f10])).
% 0.21/0.60  fof(f10,axiom,(
% 0.21/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.60  fof(f874,plain,(
% 0.21/0.60    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl7_2 | spl7_8)),
% 0.21/0.60    inference(backward_demodulation,[],[f182,f872])).
% 0.21/0.60  fof(f872,plain,(
% 0.21/0.60    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl7_2),
% 0.21/0.60    inference(forward_demodulation,[],[f844,f856])).
% 0.21/0.60  fof(f856,plain,(
% 0.21/0.60    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl7_2),
% 0.21/0.60    inference(forward_demodulation,[],[f848,f50])).
% 0.21/0.60  fof(f50,plain,(
% 0.21/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.60  fof(f848,plain,(
% 0.21/0.60    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl7_2),
% 0.21/0.60    inference(superposition,[],[f88,f837])).
% 0.21/0.60  fof(f837,plain,(
% 0.21/0.60    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) | ~spl7_2),
% 0.21/0.60    inference(forward_demodulation,[],[f421,f128])).
% 0.21/0.60  fof(f128,plain,(
% 0.21/0.60    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl7_2),
% 0.21/0.60    inference(avatar_component_clause,[],[f127])).
% 0.21/0.60  fof(f127,plain,(
% 0.21/0.60    spl7_2 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.60  fof(f421,plain,(
% 0.21/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))),
% 0.21/0.60    inference(resolution,[],[f89,f94])).
% 0.21/0.60  fof(f94,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.60    inference(definition_unfolding,[],[f61,f58])).
% 0.21/0.60  fof(f58,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,axiom,(
% 0.21/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.60  fof(f61,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f7])).
% 0.21/0.60  % (464)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.60  fof(f89,plain,(
% 0.21/0.60    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 0.21/0.60    inference(definition_unfolding,[],[f46,f86,f86])).
% 0.21/0.60  fof(f86,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f55,f85])).
% 0.21/0.60  fof(f85,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f62,f84])).
% 0.21/0.60  fof(f84,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f69,f83])).
% 0.21/0.60  fof(f83,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f79,f82])).
% 0.21/0.60  fof(f82,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f80,f81])).
% 0.21/0.60  fof(f81,plain,(
% 0.21/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f20,axiom,(
% 0.21/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.60  fof(f80,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f19])).
% 0.21/0.60  fof(f19,axiom,(
% 0.21/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.60  fof(f79,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f18])).
% 0.21/0.60  fof(f18,axiom,(
% 0.21/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.60  fof(f69,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f17])).
% 0.21/0.60  fof(f17,axiom,(
% 0.21/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.60  fof(f62,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.60  fof(f55,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f15])).
% 0.21/0.60  fof(f15,axiom,(
% 0.21/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.21/0.60    inference(cnf_transformation,[],[f34])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.60    inference(ennf_transformation,[],[f23])).
% 0.21/0.60  fof(f23,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.60    inference(negated_conjecture,[],[f22])).
% 0.21/0.60  fof(f22,conjecture,(
% 0.21/0.60    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.21/0.60  fof(f88,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f57,f58])).
% 0.21/0.60  fof(f57,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.60  fof(f844,plain,(
% 0.21/0.60    k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl7_2),
% 0.21/0.60    inference(superposition,[],[f88,f837])).
% 0.21/0.60  fof(f182,plain,(
% 0.21/0.60    ~r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) | spl7_8),
% 0.21/0.60    inference(avatar_component_clause,[],[f175])).
% 0.21/0.60  fof(f175,plain,(
% 0.21/0.60    spl7_8 <=> r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.60  fof(f855,plain,(
% 0.21/0.60    ~spl7_8 | spl7_7 | ~spl7_2),
% 0.21/0.60    inference(avatar_split_clause,[],[f854,f127,f169,f175])).
% 0.21/0.60  fof(f169,plain,(
% 0.21/0.60    spl7_7 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.60  fof(f854,plain,(
% 0.21/0.60    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) ) | ~spl7_2),
% 0.21/0.60    inference(forward_demodulation,[],[f847,f50])).
% 0.21/0.61  % (466)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.61  fof(f847,plain,(
% 0.21/0.61    ( ! [X3] : (~r2_hidden(X3,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) ) | ~spl7_2),
% 0.21/0.61    inference(superposition,[],[f92,f837])).
% 0.21/0.61  fof(f92,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.61    inference(definition_unfolding,[],[f60,f58])).
% 0.21/0.61  fof(f60,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f38])).
% 0.21/0.61  fof(f38,plain,(
% 0.21/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f37])).
% 0.21/0.61  fof(f37,plain,(
% 0.21/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.61    introduced(choice_axiom,[])).
% 0.21/0.61  fof(f28,plain,(
% 0.21/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.61    inference(ennf_transformation,[],[f25])).
% 0.21/0.61  fof(f25,plain,(
% 0.21/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.61    inference(rectify,[],[f3])).
% 0.21/0.61  fof(f3,axiom,(
% 0.21/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.61  fof(f626,plain,(
% 0.21/0.61    spl7_29 | spl7_2 | spl7_23 | spl7_4 | ~spl7_12),
% 0.21/0.61    inference(avatar_split_clause,[],[f624,f229,f133,f330,f127,f428])).
% 0.21/0.61  fof(f428,plain,(
% 0.21/0.61    spl7_29 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.61  fof(f330,plain,(
% 0.21/0.61    spl7_23 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.61  fof(f133,plain,(
% 0.21/0.61    spl7_4 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.61  fof(f229,plain,(
% 0.21/0.61    spl7_12 <=> sK1 = sK2),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.61  fof(f624,plain,(
% 0.21/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3) | ~spl7_12),
% 0.21/0.61    inference(resolution,[],[f423,f100])).
% 0.21/0.61  fof(f100,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0) )),
% 0.21/0.61    inference(definition_unfolding,[],[f64,f86,f87,f87,f86])).
% 0.21/0.61  fof(f87,plain,(
% 0.21/0.61    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.61    inference(definition_unfolding,[],[f51,f86])).
% 0.21/0.61  fof(f51,plain,(
% 0.21/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f14])).
% 0.21/0.61  fof(f14,axiom,(
% 0.21/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.61  fof(f64,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f40])).
% 0.21/0.61  fof(f40,plain,(
% 0.21/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.61    inference(flattening,[],[f39])).
% 0.21/0.61  fof(f39,plain,(
% 0.21/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.61    inference(nnf_transformation,[],[f31])).
% 0.21/0.61  fof(f31,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.61    inference(ennf_transformation,[],[f21])).
% 0.21/0.61  fof(f21,axiom,(
% 0.21/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.61  fof(f423,plain,(
% 0.21/0.61    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3)) | ~spl7_12),
% 0.21/0.61    inference(backward_demodulation,[],[f89,f230])).
% 0.21/0.61  fof(f230,plain,(
% 0.21/0.61    sK1 = sK2 | ~spl7_12),
% 0.21/0.61    inference(avatar_component_clause,[],[f229])).
% 0.21/0.61  fof(f622,plain,(
% 0.21/0.61    ~spl7_12 | ~spl7_20 | ~spl7_29),
% 0.21/0.61    inference(avatar_contradiction_clause,[],[f615])).
% 0.21/0.61  fof(f615,plain,(
% 0.21/0.61    $false | (~spl7_12 | ~spl7_20 | ~spl7_29)),
% 0.21/0.61    inference(subsumption_resolution,[],[f424,f611])).
% 0.21/0.61  fof(f611,plain,(
% 0.21/0.61    sK0 = sK1 | (~spl7_20 | ~spl7_29)),
% 0.21/0.61    inference(resolution,[],[f598,f117])).
% 0.21/0.61  fof(f117,plain,(
% 0.21/0.61    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 0.21/0.61    inference(equality_resolution,[],[f116])).
% 0.21/0.61  fof(f116,plain,(
% 0.21/0.61    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 0.21/0.61    inference(equality_resolution,[],[f107])).
% 0.21/0.61  fof(f107,plain,(
% 0.21/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.61    inference(definition_unfolding,[],[f73,f85])).
% 0.21/0.61  fof(f73,plain,(
% 0.21/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.61    inference(cnf_transformation,[],[f45])).
% 0.21/0.61  fof(f45,plain,(
% 0.21/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK6(X0,X1,X2,X3) != X2 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X2 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X0 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 0.21/0.61  fof(f44,plain,(
% 0.21/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X2 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X2 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X0 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.21/0.61    introduced(choice_axiom,[])).
% 0.21/0.61  fof(f43,plain,(
% 0.21/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.61    inference(rectify,[],[f42])).
% 0.21/0.61  fof(f42,plain,(
% 0.21/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.61    inference(flattening,[],[f41])).
% 0.21/0.61  fof(f41,plain,(
% 0.21/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.61    inference(nnf_transformation,[],[f32])).
% 0.21/0.61  fof(f32,plain,(
% 0.21/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.61    inference(ennf_transformation,[],[f12])).
% 0.21/0.61  fof(f12,axiom,(
% 0.21/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.61  fof(f598,plain,(
% 0.21/0.61    ( ! [X6] : (~r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X6) ) | (~spl7_20 | ~spl7_29)),
% 0.21/0.61    inference(duplicate_literal_removal,[],[f593])).
% 0.21/0.61  fof(f593,plain,(
% 0.21/0.61    ( ! [X6] : (~r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X6 | sK1 = X6 | sK1 = X6) ) | (~spl7_20 | ~spl7_29)),
% 0.21/0.61    inference(superposition,[],[f120,f537])).
% 0.21/0.61  fof(f537,plain,(
% 0.21/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | (~spl7_20 | ~spl7_29)),
% 0.21/0.61    inference(backward_demodulation,[],[f429,f313])).
% 0.21/0.61  fof(f313,plain,(
% 0.21/0.61    sK1 = sK3 | ~spl7_20),
% 0.21/0.61    inference(avatar_component_clause,[],[f312])).
% 0.21/0.61  fof(f312,plain,(
% 0.21/0.61    spl7_20 <=> sK1 = sK3),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.61  fof(f429,plain,(
% 0.21/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK3) | ~spl7_29),
% 0.21/0.61    inference(avatar_component_clause,[],[f428])).
% 0.21/0.61  fof(f120,plain,(
% 0.21/0.61    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.21/0.61    inference(equality_resolution,[],[f109])).
% 0.21/0.61  fof(f109,plain,(
% 0.21/0.61    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.61    inference(definition_unfolding,[],[f71,f85])).
% 0.21/0.61  % (460)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.61  fof(f71,plain,(
% 0.21/0.61    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.61    inference(cnf_transformation,[],[f45])).
% 0.21/0.61  fof(f424,plain,(
% 0.21/0.61    sK0 != sK1 | ~spl7_12),
% 0.21/0.61    inference(superposition,[],[f47,f230])).
% 0.21/0.61  fof(f47,plain,(
% 0.21/0.61    sK0 != sK2),
% 0.21/0.61    inference(cnf_transformation,[],[f34])).
% 0.21/0.61  fof(f535,plain,(
% 0.21/0.61    spl7_20 | spl7_21 | ~spl7_29),
% 0.21/0.61    inference(avatar_split_clause,[],[f534,f428,f315,f312])).
% 0.21/0.61  fof(f315,plain,(
% 0.21/0.61    spl7_21 <=> sK0 = sK3),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.61  fof(f534,plain,(
% 0.21/0.61    sK0 = sK3 | sK1 = sK3 | ~spl7_29),
% 0.21/0.61    inference(duplicate_literal_removal,[],[f533])).
% 0.21/0.61  fof(f533,plain,(
% 0.21/0.61    sK0 = sK3 | sK0 = sK3 | sK1 = sK3 | ~spl7_29),
% 0.21/0.61    inference(resolution,[],[f509,f120])).
% 0.21/0.61  fof(f509,plain,(
% 0.21/0.61    r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_29),
% 0.21/0.61    inference(superposition,[],[f115,f429])).
% 0.21/0.61  fof(f115,plain,(
% 0.21/0.61    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 0.21/0.61    inference(equality_resolution,[],[f114])).
% 0.21/0.61  fof(f114,plain,(
% 0.21/0.61    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 0.21/0.61    inference(equality_resolution,[],[f106])).
% 0.21/0.61  fof(f106,plain,(
% 0.21/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.61    inference(definition_unfolding,[],[f74,f85])).
% 0.21/0.61  fof(f74,plain,(
% 0.21/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.61    inference(cnf_transformation,[],[f45])).
% 0.21/0.61  fof(f495,plain,(
% 0.21/0.61    ~spl7_12 | ~spl7_23),
% 0.21/0.61    inference(avatar_contradiction_clause,[],[f486])).
% 0.21/0.61  fof(f486,plain,(
% 0.21/0.61    $false | (~spl7_12 | ~spl7_23)),
% 0.21/0.61    inference(subsumption_resolution,[],[f424,f481])).
% 0.21/0.61  fof(f481,plain,(
% 0.21/0.61    sK0 = sK1 | ~spl7_23),
% 0.21/0.61    inference(resolution,[],[f445,f117])).
% 0.21/0.61  fof(f445,plain,(
% 0.21/0.61    ( ! [X6] : (~r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X6) ) | ~spl7_23),
% 0.21/0.61    inference(duplicate_literal_removal,[],[f440])).
% 0.21/0.61  fof(f440,plain,(
% 0.21/0.61    ( ! [X6] : (~r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X6 | sK1 = X6 | sK1 = X6) ) | ~spl7_23),
% 0.21/0.61    inference(superposition,[],[f120,f331])).
% 0.21/0.61  fof(f331,plain,(
% 0.21/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl7_23),
% 0.21/0.61    inference(avatar_component_clause,[],[f330])).
% 0.21/0.61  fof(f422,plain,(
% 0.21/0.61    spl7_1 | spl7_2 | spl7_3 | spl7_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f420,f133,f130,f127,f124])).
% 0.21/0.61  fof(f124,plain,(
% 0.21/0.61    spl7_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.61  fof(f130,plain,(
% 0.21/0.61    spl7_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 0.21/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.61  fof(f420,plain,(
% 0.21/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 0.21/0.61    inference(resolution,[],[f89,f100])).
% 0.21/0.61  % (451)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.61  % (456)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.61  % (458)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.61  % (454)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.61  % (455)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.61  % (451)Refutation not found, incomplete strategy% (451)------------------------------
% 0.21/0.61  % (451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (449)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.62  % (471)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.62  % (451)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.62  
% 0.21/0.62  % (451)Memory used [KB]: 10618
% 0.21/0.62  % (451)Time elapsed: 0.149 s
% 0.21/0.62  % (451)------------------------------
% 0.21/0.62  % (451)------------------------------
% 0.21/0.62  fof(f419,plain,(
% 0.21/0.62    ~spl7_21),
% 0.21/0.62    inference(avatar_contradiction_clause,[],[f416])).
% 0.21/0.62  fof(f416,plain,(
% 0.21/0.62    $false | ~spl7_21),
% 0.21/0.62    inference(subsumption_resolution,[],[f48,f316])).
% 0.21/0.62  fof(f316,plain,(
% 0.21/0.62    sK0 = sK3 | ~spl7_21),
% 0.21/0.62    inference(avatar_component_clause,[],[f315])).
% 0.21/0.62  fof(f48,plain,(
% 0.21/0.62    sK0 != sK3),
% 0.21/0.62    inference(cnf_transformation,[],[f34])).
% 0.21/0.62  fof(f395,plain,(
% 0.21/0.62    ~spl7_4 | ~spl7_20),
% 0.21/0.62    inference(avatar_contradiction_clause,[],[f388])).
% 0.21/0.62  fof(f388,plain,(
% 0.21/0.62    $false | (~spl7_4 | ~spl7_20)),
% 0.21/0.62    inference(subsumption_resolution,[],[f323,f380])).
% 0.21/0.62  fof(f380,plain,(
% 0.21/0.62    sK0 = sK1 | (~spl7_4 | ~spl7_20)),
% 0.21/0.62    inference(resolution,[],[f346,f117])).
% 0.21/0.62  fof(f346,plain,(
% 0.21/0.62    ( ! [X6] : (~r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X6) ) | (~spl7_4 | ~spl7_20)),
% 0.21/0.62    inference(duplicate_literal_removal,[],[f341])).
% 0.21/0.62  fof(f341,plain,(
% 0.21/0.62    ( ! [X6] : (~r2_hidden(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X6 | sK1 = X6 | sK1 = X6) ) | (~spl7_4 | ~spl7_20)),
% 0.21/0.62    inference(superposition,[],[f120,f320])).
% 0.21/0.62  fof(f320,plain,(
% 0.21/0.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | (~spl7_4 | ~spl7_20)),
% 0.21/0.62    inference(backward_demodulation,[],[f134,f313])).
% 0.21/0.62  fof(f134,plain,(
% 0.21/0.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~spl7_4),
% 0.21/0.62    inference(avatar_component_clause,[],[f133])).
% 0.21/0.62  fof(f323,plain,(
% 0.21/0.62    sK0 != sK1 | ~spl7_20),
% 0.21/0.62    inference(superposition,[],[f48,f313])).
% 0.21/0.62  fof(f317,plain,(
% 0.21/0.62    spl7_20 | spl7_21 | ~spl7_4),
% 0.21/0.62    inference(avatar_split_clause,[],[f310,f133,f315,f312])).
% 0.21/0.62  fof(f310,plain,(
% 0.21/0.62    sK0 = sK3 | sK1 = sK3 | ~spl7_4),
% 0.21/0.62    inference(duplicate_literal_removal,[],[f309])).
% 0.21/0.62  fof(f309,plain,(
% 0.21/0.62    sK0 = sK3 | sK0 = sK3 | sK1 = sK3 | ~spl7_4),
% 0.21/0.62    inference(resolution,[],[f270,f120])).
% 0.21/0.62  fof(f270,plain,(
% 0.21/0.62    r2_hidden(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_4),
% 0.21/0.62    inference(superposition,[],[f119,f134])).
% 0.21/0.62  fof(f119,plain,(
% 0.21/0.62    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 0.21/0.62    inference(equality_resolution,[],[f118])).
% 0.21/0.62  fof(f118,plain,(
% 0.21/0.62    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 0.21/0.62    inference(equality_resolution,[],[f108])).
% 0.21/0.62  fof(f108,plain,(
% 0.21/0.62    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.62    inference(definition_unfolding,[],[f72,f85])).
% 0.21/0.62  fof(f72,plain,(
% 0.21/0.62    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.62    inference(cnf_transformation,[],[f45])).
% 0.21/0.62  fof(f257,plain,(
% 0.21/0.62    ~spl7_13),
% 0.21/0.62    inference(avatar_contradiction_clause,[],[f254])).
% 0.21/0.62  fof(f254,plain,(
% 0.21/0.62    $false | ~spl7_13),
% 0.21/0.62    inference(subsumption_resolution,[],[f47,f233])).
% 0.21/0.62  fof(f233,plain,(
% 0.21/0.62    sK0 = sK2 | ~spl7_13),
% 0.21/0.62    inference(avatar_component_clause,[],[f232])).
% 0.21/0.62  fof(f232,plain,(
% 0.21/0.62    spl7_13 <=> sK0 = sK2),
% 0.21/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.62  fof(f253,plain,(
% 0.21/0.62    spl7_12 | spl7_13 | ~spl7_1),
% 0.21/0.62    inference(avatar_split_clause,[],[f252,f124,f232,f229])).
% 0.21/0.62  fof(f252,plain,(
% 0.21/0.62    sK0 = sK2 | sK1 = sK2 | ~spl7_1),
% 0.21/0.62    inference(duplicate_literal_removal,[],[f251])).
% 0.21/0.62  fof(f251,plain,(
% 0.21/0.62    sK0 = sK2 | sK0 = sK2 | sK1 = sK2 | ~spl7_1),
% 0.21/0.62    inference(resolution,[],[f243,f120])).
% 0.21/0.62  fof(f243,plain,(
% 0.21/0.62    r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_1),
% 0.21/0.62    inference(superposition,[],[f119,f125])).
% 0.21/0.62  fof(f125,plain,(
% 0.21/0.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) | ~spl7_1),
% 0.21/0.62    inference(avatar_component_clause,[],[f124])).
% 0.21/0.62  fof(f234,plain,(
% 0.21/0.62    spl7_12 | spl7_13 | ~spl7_3),
% 0.21/0.62    inference(avatar_split_clause,[],[f227,f130,f232,f229])).
% 0.21/0.62  fof(f227,plain,(
% 0.21/0.62    sK0 = sK2 | sK1 = sK2 | ~spl7_3),
% 0.21/0.62    inference(duplicate_literal_removal,[],[f226])).
% 0.21/0.62  fof(f226,plain,(
% 0.21/0.62    sK0 = sK2 | sK0 = sK2 | sK1 = sK2 | ~spl7_3),
% 0.21/0.62    inference(resolution,[],[f219,f120])).
% 0.21/0.62  fof(f219,plain,(
% 0.21/0.62    r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_3),
% 0.21/0.62    inference(superposition,[],[f119,f131])).
% 0.21/0.62  fof(f131,plain,(
% 0.21/0.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl7_3),
% 0.21/0.62    inference(avatar_component_clause,[],[f130])).
% 0.21/0.62  fof(f190,plain,(
% 0.21/0.62    ~spl7_2 | ~spl7_7),
% 0.21/0.62    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.62  fof(f186,plain,(
% 0.21/0.62    $false | (~spl7_2 | ~spl7_7)),
% 0.21/0.62    inference(subsumption_resolution,[],[f145,f170])).
% 0.21/0.62  fof(f170,plain,(
% 0.21/0.62    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl7_7),
% 0.21/0.62    inference(avatar_component_clause,[],[f169])).
% 0.21/0.62  fof(f145,plain,(
% 0.21/0.62    r2_hidden(sK1,k1_xboole_0) | ~spl7_2),
% 0.21/0.62    inference(superposition,[],[f115,f128])).
% 0.21/0.62  % SZS output end Proof for theBenchmark
% 0.21/0.62  % (442)------------------------------
% 0.21/0.62  % (442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.62  % (442)Termination reason: Refutation
% 0.21/0.62  
% 0.21/0.62  % (442)Memory used [KB]: 11001
% 0.21/0.62  % (442)Time elapsed: 0.166 s
% 0.21/0.62  % (442)------------------------------
% 0.21/0.62  % (442)------------------------------
% 0.21/0.62  % (470)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.78/0.62  % (445)Refutation not found, incomplete strategy% (445)------------------------------
% 1.78/0.62  % (445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.62  % (445)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.62  
% 1.78/0.62  % (445)Memory used [KB]: 6524
% 1.78/0.62  % (445)Time elapsed: 0.176 s
% 1.78/0.62  % (445)------------------------------
% 1.78/0.62  % (445)------------------------------
% 1.78/0.62  % (453)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.78/0.62  % (439)Success in time 0.254 s
%------------------------------------------------------------------------------
