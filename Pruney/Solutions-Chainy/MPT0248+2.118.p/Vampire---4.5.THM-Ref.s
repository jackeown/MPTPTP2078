%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:07 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 387 expanded)
%              Number of leaves         :   29 ( 131 expanded)
%              Depth                    :   15
%              Number of atoms          :  401 ( 910 expanded)
%              Number of equality atoms :  173 ( 644 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f415,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f132,f139,f185,f351,f364,f365,f414])).

fof(f414,plain,
    ( ~ spl7_1
    | spl7_5
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | ~ spl7_1
    | spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f412,f138])).

fof(f138,plain,
    ( sK2 != sK3
    | spl7_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl7_5
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f412,plain,
    ( sK2 = sK3
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f410,f389])).

fof(f389,plain,
    ( sK2 = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f89,f117])).

fof(f117,plain,
    ( sK2 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_1
  <=> sK2 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f89,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f45,f85,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f83])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_xboole_0 != sK3
      | sK2 != k1_tarski(sK1) )
    & ( sK3 != k1_tarski(sK1)
      | k1_xboole_0 != sK2 )
    & ( sK3 != k1_tarski(sK1)
      | sK2 != k1_tarski(sK1) )
    & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK3
        | sK2 != k1_tarski(sK1) )
      & ( sK3 != k1_tarski(sK1)
        | k1_xboole_0 != sK2 )
      & ( sK3 != k1_tarski(sK1)
        | sK2 != k1_tarski(sK1) )
      & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f410,plain,
    ( sK3 = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(resolution,[],[f396,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f57,f84])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f396,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(resolution,[],[f370,f350])).

fof(f350,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl7_9
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f370,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | r1_tarski(sK2,X1) )
    | ~ spl7_1 ),
    inference(superposition,[],[f100,f117])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f85])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f365,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f316,f125,f116])).

fof(f125,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f316,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f99,f142])).

fof(f142,plain,(
    r1_tarski(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f90,f89])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f84])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

% (23495)Refutation not found, incomplete strategy% (23495)------------------------------
% (23495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23495)Termination reason: Refutation not found, incomplete strategy

% (23495)Memory used [KB]: 1663
% (23495)Time elapsed: 0.116 s
% (23495)------------------------------
% (23495)------------------------------
fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f64,f85,f85])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f364,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f344,f131])).

fof(f131,plain,
    ( sK3 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_4
  <=> sK3 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f344,plain,
    ( sK3 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f343,f248])).

fof(f248,plain,(
    ! [X0] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(resolution,[],[f247,f92])).

fof(f247,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f244,f162])).

fof(f162,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f158,f91])).

fof(f91,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f53,f84])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f158,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) ),
    inference(resolution,[],[f102,f90])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f70,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f244,plain,(
    ! [X0] :
      ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f103,f228])).

fof(f228,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f223,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f223,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f221,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f221,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(superposition,[],[f59,f91])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f56])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

% (23494)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f343,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3))
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f89,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f351,plain,
    ( spl7_2
    | spl7_9
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f346,f182,f348,f120])).

fof(f120,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f182,plain,
    ( spl7_7
  <=> sK1 = sK4(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f346,plain,
    ( r2_hidden(sK1,sK3)
    | k1_xboole_0 = sK3
    | ~ spl7_7 ),
    inference(superposition,[],[f51,f184])).

fof(f184,plain,
    ( sK1 = sK4(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f182])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f185,plain,
    ( spl7_2
    | spl7_7 ),
    inference(avatar_split_clause,[],[f180,f182,f120])).

fof(f180,plain,
    ( sK1 = sK4(sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f178,f51])).

fof(f178,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3)
      | sK1 = X2 ) ),
    inference(resolution,[],[f111,f146])).

fof(f146,plain,(
    ! [X3] :
      ( r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X3,sK3) ) ),
    inference(resolution,[],[f77,f141])).

fof(f141,plain,(
    sP0(sK3,sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f114,f89])).

fof(f114,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f81,f84])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & ~ r2_hidden(sK6(X0,X1,X2),X1) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & ~ r2_hidden(sK6(X0,X1,X2),X1) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f111,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f60,f85])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f139,plain,
    ( ~ spl7_5
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f134,f116,f136])).

fof(f134,plain,
    ( sK2 != k2_enumset1(sK1,sK1,sK1,sK1)
    | sK2 != sK3 ),
    inference(inner_rewriting,[],[f133])).

fof(f133,plain,
    ( sK3 != k2_enumset1(sK1,sK1,sK1,sK1)
    | sK2 != sK3 ),
    inference(inner_rewriting,[],[f88])).

fof(f88,plain,
    ( sK3 != k2_enumset1(sK1,sK1,sK1,sK1)
    | sK2 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f46,f85,f85])).

fof(f46,plain,
    ( sK3 != k1_tarski(sK1)
    | sK2 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f132,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f87,f129,f125])).

fof(f87,plain,
    ( sK3 != k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f47,f85])).

fof(f47,plain,
    ( sK3 != k1_tarski(sK1)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f123,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f86,f120,f116])).

fof(f86,plain,
    ( k1_xboole_0 != sK3
    | sK2 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f48,f85])).

fof(f48,plain,
    ( k1_xboole_0 != sK3
    | sK2 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:46:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (23502)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (23500)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (23496)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (23499)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.53  % (23520)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.23/0.53  % (23512)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.23/0.53  % (23500)Refutation found. Thanks to Tanya!
% 1.23/0.53  % SZS status Theorem for theBenchmark
% 1.23/0.53  % (23516)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.53  % (23508)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.54  % (23495)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.54  % SZS output start Proof for theBenchmark
% 1.23/0.54  fof(f415,plain,(
% 1.23/0.54    $false),
% 1.23/0.54    inference(avatar_sat_refutation,[],[f123,f132,f139,f185,f351,f364,f365,f414])).
% 1.23/0.54  fof(f414,plain,(
% 1.23/0.54    ~spl7_1 | spl7_5 | ~spl7_9),
% 1.23/0.54    inference(avatar_contradiction_clause,[],[f413])).
% 1.23/0.54  fof(f413,plain,(
% 1.23/0.54    $false | (~spl7_1 | spl7_5 | ~spl7_9)),
% 1.23/0.54    inference(subsumption_resolution,[],[f412,f138])).
% 1.23/0.54  fof(f138,plain,(
% 1.23/0.54    sK2 != sK3 | spl7_5),
% 1.23/0.54    inference(avatar_component_clause,[],[f136])).
% 1.23/0.54  fof(f136,plain,(
% 1.23/0.54    spl7_5 <=> sK2 = sK3),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.23/0.54  fof(f412,plain,(
% 1.23/0.54    sK2 = sK3 | (~spl7_1 | ~spl7_9)),
% 1.23/0.54    inference(forward_demodulation,[],[f410,f389])).
% 1.23/0.54  fof(f389,plain,(
% 1.23/0.54    sK2 = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl7_1),
% 1.23/0.54    inference(forward_demodulation,[],[f89,f117])).
% 1.23/0.54  fof(f117,plain,(
% 1.23/0.54    sK2 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl7_1),
% 1.23/0.54    inference(avatar_component_clause,[],[f116])).
% 1.23/0.54  fof(f116,plain,(
% 1.23/0.54    spl7_1 <=> sK2 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.23/0.54  fof(f89,plain,(
% 1.23/0.54    k2_enumset1(sK1,sK1,sK1,sK1) = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.23/0.54    inference(definition_unfolding,[],[f45,f85,f84])).
% 1.23/0.54  fof(f84,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.23/0.54    inference(definition_unfolding,[],[f54,f83])).
% 1.23/0.54  fof(f83,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f55,f71])).
% 1.23/0.54  fof(f71,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f14])).
% 1.23/0.54  fof(f14,axiom,(
% 1.23/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.23/0.54  fof(f55,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f13])).
% 1.23/0.54  fof(f13,axiom,(
% 1.23/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.23/0.54  fof(f54,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.23/0.54    inference(cnf_transformation,[],[f17])).
% 1.23/0.54  fof(f17,axiom,(
% 1.23/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.23/0.54  fof(f85,plain,(
% 1.23/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f50,f83])).
% 1.23/0.54  fof(f50,plain,(
% 1.23/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f12])).
% 1.23/0.54  fof(f12,axiom,(
% 1.23/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.23/0.54  fof(f45,plain,(
% 1.23/0.54    k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 1.23/0.54    inference(cnf_transformation,[],[f27])).
% 1.23/0.54  fof(f27,plain,(
% 1.23/0.54    (k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 1.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f26])).
% 1.23/0.54  fof(f26,plain,(
% 1.23/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3))),
% 1.23/0.54    introduced(choice_axiom,[])).
% 1.23/0.54  fof(f20,plain,(
% 1.23/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.23/0.54    inference(ennf_transformation,[],[f19])).
% 1.23/0.54  fof(f19,negated_conjecture,(
% 1.23/0.54    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.23/0.54    inference(negated_conjecture,[],[f18])).
% 1.23/0.54  fof(f18,conjecture,(
% 1.23/0.54    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.23/0.54  fof(f410,plain,(
% 1.23/0.54    sK3 = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK3)) | (~spl7_1 | ~spl7_9)),
% 1.23/0.54    inference(resolution,[],[f396,f92])).
% 1.23/0.54  fof(f92,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1) )),
% 1.23/0.54    inference(definition_unfolding,[],[f57,f84])).
% 1.23/0.54  fof(f57,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f22])).
% 1.23/0.54  fof(f22,plain,(
% 1.23/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.23/0.54    inference(ennf_transformation,[],[f6])).
% 1.23/0.54  fof(f6,axiom,(
% 1.23/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.23/0.54  fof(f396,plain,(
% 1.23/0.54    r1_tarski(sK2,sK3) | (~spl7_1 | ~spl7_9)),
% 1.23/0.54    inference(resolution,[],[f370,f350])).
% 1.23/0.54  fof(f350,plain,(
% 1.23/0.54    r2_hidden(sK1,sK3) | ~spl7_9),
% 1.23/0.54    inference(avatar_component_clause,[],[f348])).
% 1.23/0.54  fof(f348,plain,(
% 1.23/0.54    spl7_9 <=> r2_hidden(sK1,sK3)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.23/0.54  fof(f370,plain,(
% 1.23/0.54    ( ! [X1] : (~r2_hidden(sK1,X1) | r1_tarski(sK2,X1)) ) | ~spl7_1),
% 1.23/0.54    inference(superposition,[],[f100,f117])).
% 1.23/0.54  fof(f100,plain,(
% 1.23/0.54    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f68,f85])).
% 1.23/0.54  fof(f68,plain,(
% 1.23/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f37])).
% 1.23/0.54  fof(f37,plain,(
% 1.23/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.23/0.54    inference(nnf_transformation,[],[f15])).
% 1.23/0.54  fof(f15,axiom,(
% 1.23/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.23/0.54  fof(f365,plain,(
% 1.23/0.54    spl7_1 | spl7_3),
% 1.23/0.54    inference(avatar_split_clause,[],[f316,f125,f116])).
% 1.23/0.54  fof(f125,plain,(
% 1.23/0.54    spl7_3 <=> k1_xboole_0 = sK2),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.23/0.54  fof(f316,plain,(
% 1.23/0.54    k1_xboole_0 = sK2 | sK2 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.23/0.54    inference(resolution,[],[f99,f142])).
% 1.23/0.54  fof(f142,plain,(
% 1.23/0.54    r1_tarski(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.23/0.54    inference(superposition,[],[f90,f89])).
% 1.23/0.54  fof(f90,plain,(
% 1.23/0.54    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.23/0.54    inference(definition_unfolding,[],[f52,f84])).
% 1.23/0.54  fof(f52,plain,(
% 1.23/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.23/0.54    inference(cnf_transformation,[],[f10])).
% 1.23/0.54  % (23495)Refutation not found, incomplete strategy% (23495)------------------------------
% 1.23/0.54  % (23495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (23495)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (23495)Memory used [KB]: 1663
% 1.23/0.54  % (23495)Time elapsed: 0.116 s
% 1.23/0.54  % (23495)------------------------------
% 1.23/0.54  % (23495)------------------------------
% 1.23/0.54  fof(f10,axiom,(
% 1.23/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.23/0.54  fof(f99,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.23/0.54    inference(definition_unfolding,[],[f64,f85,f85])).
% 1.23/0.54  fof(f64,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.23/0.54    inference(cnf_transformation,[],[f36])).
% 1.23/0.54  fof(f36,plain,(
% 1.23/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.23/0.54    inference(flattening,[],[f35])).
% 1.23/0.54  fof(f35,plain,(
% 1.23/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.23/0.54    inference(nnf_transformation,[],[f16])).
% 1.23/0.54  fof(f16,axiom,(
% 1.23/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.23/0.54  fof(f364,plain,(
% 1.23/0.54    ~spl7_3 | spl7_4),
% 1.23/0.54    inference(avatar_contradiction_clause,[],[f363])).
% 1.23/0.54  fof(f363,plain,(
% 1.23/0.54    $false | (~spl7_3 | spl7_4)),
% 1.23/0.54    inference(subsumption_resolution,[],[f344,f131])).
% 1.23/0.54  fof(f131,plain,(
% 1.23/0.54    sK3 != k2_enumset1(sK1,sK1,sK1,sK1) | spl7_4),
% 1.23/0.54    inference(avatar_component_clause,[],[f129])).
% 1.23/0.54  fof(f129,plain,(
% 1.23/0.54    spl7_4 <=> sK3 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.23/0.54  fof(f344,plain,(
% 1.23/0.54    sK3 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl7_3),
% 1.23/0.54    inference(forward_demodulation,[],[f343,f248])).
% 1.23/0.54  fof(f248,plain,(
% 1.23/0.54    ( ! [X0] : (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.23/0.54    inference(resolution,[],[f247,f92])).
% 1.23/0.54  fof(f247,plain,(
% 1.23/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f244,f162])).
% 1.23/0.54  fof(f162,plain,(
% 1.23/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.23/0.54    inference(forward_demodulation,[],[f158,f91])).
% 1.23/0.54  fof(f91,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = X0) )),
% 1.23/0.54    inference(definition_unfolding,[],[f53,f84])).
% 1.23/0.54  fof(f53,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.23/0.54    inference(cnf_transformation,[],[f7])).
% 1.23/0.54  fof(f7,axiom,(
% 1.23/0.54    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.23/0.54  fof(f158,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) )),
% 1.23/0.54    inference(resolution,[],[f102,f90])).
% 1.23/0.54  fof(f102,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.23/0.54    inference(definition_unfolding,[],[f70,f56])).
% 1.23/0.54  fof(f56,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.23/0.54    inference(cnf_transformation,[],[f5])).
% 1.23/0.54  fof(f5,axiom,(
% 1.23/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.23/0.54  fof(f70,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f38])).
% 1.23/0.54  fof(f38,plain,(
% 1.23/0.54    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.23/0.54    inference(nnf_transformation,[],[f4])).
% 1.23/0.54  fof(f4,axiom,(
% 1.23/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.23/0.54  fof(f244,plain,(
% 1.23/0.54    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.23/0.54    inference(superposition,[],[f103,f228])).
% 1.23/0.54  fof(f228,plain,(
% 1.23/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.23/0.54    inference(resolution,[],[f223,f58])).
% 1.23/0.54  fof(f58,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.23/0.54    inference(cnf_transformation,[],[f30])).
% 1.23/0.54  fof(f30,plain,(
% 1.23/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.23/0.54    inference(nnf_transformation,[],[f2])).
% 1.23/0.54  fof(f2,axiom,(
% 1.23/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.23/0.54  fof(f223,plain,(
% 1.23/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.23/0.54    inference(resolution,[],[f221,f104])).
% 1.23/0.54  fof(f104,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | r1_xboole_0(X0,X2)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f74,f84])).
% 1.23/0.54  fof(f74,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f23])).
% 1.23/0.54  fof(f23,plain,(
% 1.23/0.54    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.23/0.54    inference(ennf_transformation,[],[f9])).
% 1.23/0.54  fof(f9,axiom,(
% 1.23/0.54    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.23/0.54  fof(f221,plain,(
% 1.23/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 1.23/0.54    inference(equality_resolution,[],[f148])).
% 1.23/0.54  fof(f148,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.23/0.54    inference(superposition,[],[f59,f91])).
% 1.23/0.54  fof(f59,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f30])).
% 1.23/0.54  fof(f103,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f69,f56])).
% 1.23/0.54  fof(f69,plain,(
% 1.23/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f38])).
% 1.23/0.54  % (23494)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.23/0.54  fof(f343,plain,(
% 1.23/0.54    k2_enumset1(sK1,sK1,sK1,sK1) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)) | ~spl7_3),
% 1.23/0.54    inference(forward_demodulation,[],[f89,f126])).
% 1.23/0.54  fof(f126,plain,(
% 1.23/0.54    k1_xboole_0 = sK2 | ~spl7_3),
% 1.23/0.54    inference(avatar_component_clause,[],[f125])).
% 1.23/0.54  fof(f351,plain,(
% 1.23/0.54    spl7_2 | spl7_9 | ~spl7_7),
% 1.23/0.54    inference(avatar_split_clause,[],[f346,f182,f348,f120])).
% 1.23/0.54  fof(f120,plain,(
% 1.23/0.54    spl7_2 <=> k1_xboole_0 = sK3),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.23/0.54  fof(f182,plain,(
% 1.23/0.54    spl7_7 <=> sK1 = sK4(sK3)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.23/0.54  fof(f346,plain,(
% 1.23/0.54    r2_hidden(sK1,sK3) | k1_xboole_0 = sK3 | ~spl7_7),
% 1.23/0.54    inference(superposition,[],[f51,f184])).
% 1.23/0.54  fof(f184,plain,(
% 1.23/0.54    sK1 = sK4(sK3) | ~spl7_7),
% 1.23/0.54    inference(avatar_component_clause,[],[f182])).
% 1.23/0.54  fof(f51,plain,(
% 1.23/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.23/0.54    inference(cnf_transformation,[],[f29])).
% 1.23/0.54  fof(f29,plain,(
% 1.23/0.54    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f28])).
% 1.23/0.54  fof(f28,plain,(
% 1.23/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.23/0.54    introduced(choice_axiom,[])).
% 1.23/0.54  fof(f21,plain,(
% 1.23/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.23/0.54    inference(ennf_transformation,[],[f3])).
% 1.23/0.54  fof(f3,axiom,(
% 1.23/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.23/0.54  fof(f185,plain,(
% 1.23/0.54    spl7_2 | spl7_7),
% 1.23/0.54    inference(avatar_split_clause,[],[f180,f182,f120])).
% 1.23/0.54  fof(f180,plain,(
% 1.23/0.54    sK1 = sK4(sK3) | k1_xboole_0 = sK3),
% 1.23/0.54    inference(resolution,[],[f178,f51])).
% 1.23/0.54  fof(f178,plain,(
% 1.23/0.54    ( ! [X2] : (~r2_hidden(X2,sK3) | sK1 = X2) )),
% 1.23/0.54    inference(resolution,[],[f111,f146])).
% 1.23/0.54  fof(f146,plain,(
% 1.23/0.54    ( ! [X3] : (r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X3,sK3)) )),
% 1.23/0.54    inference(resolution,[],[f77,f141])).
% 1.23/0.54  fof(f141,plain,(
% 1.23/0.54    sP0(sK3,sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.23/0.54    inference(superposition,[],[f114,f89])).
% 1.23/0.54  fof(f114,plain,(
% 1.23/0.54    ( ! [X0,X1] : (sP0(X1,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.23/0.54    inference(equality_resolution,[],[f108])).
% 1.23/0.54  fof(f108,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.23/0.54    inference(definition_unfolding,[],[f81,f84])).
% 1.23/0.54  fof(f81,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.23/0.54    inference(cnf_transformation,[],[f44])).
% 1.23/0.54  fof(f44,plain,(
% 1.23/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.23/0.54    inference(nnf_transformation,[],[f25])).
% 1.23/0.54  fof(f25,plain,(
% 1.23/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.23/0.54    inference(definition_folding,[],[f1,f24])).
% 1.23/0.54  fof(f24,plain,(
% 1.23/0.54    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.23/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.23/0.54  fof(f1,axiom,(
% 1.23/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.23/0.54  fof(f77,plain,(
% 1.23/0.54    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | r2_hidden(X4,X2)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f43])).
% 1.23/0.54  fof(f43,plain,(
% 1.23/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).
% 1.23/0.54  fof(f42,plain,(
% 1.23/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.23/0.54    introduced(choice_axiom,[])).
% 1.23/0.54  fof(f41,plain,(
% 1.23/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.23/0.54    inference(rectify,[],[f40])).
% 1.23/0.54  fof(f40,plain,(
% 1.23/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.23/0.54    inference(flattening,[],[f39])).
% 1.23/0.54  fof(f39,plain,(
% 1.23/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.23/0.54    inference(nnf_transformation,[],[f24])).
% 1.23/0.54  fof(f111,plain,(
% 1.23/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.23/0.54    inference(equality_resolution,[],[f96])).
% 1.23/0.54  fof(f96,plain,(
% 1.23/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.23/0.54    inference(definition_unfolding,[],[f60,f85])).
% 1.23/0.54  fof(f60,plain,(
% 1.23/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.23/0.54    inference(cnf_transformation,[],[f34])).
% 1.23/0.54  fof(f34,plain,(
% 1.23/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 1.23/0.54  fof(f33,plain,(
% 1.23/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.23/0.54    introduced(choice_axiom,[])).
% 1.23/0.54  fof(f32,plain,(
% 1.23/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.23/0.54    inference(rectify,[],[f31])).
% 1.23/0.54  fof(f31,plain,(
% 1.23/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.23/0.54    inference(nnf_transformation,[],[f11])).
% 1.23/0.54  fof(f11,axiom,(
% 1.23/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.23/0.54  fof(f139,plain,(
% 1.23/0.54    ~spl7_5 | ~spl7_1),
% 1.23/0.54    inference(avatar_split_clause,[],[f134,f116,f136])).
% 1.23/0.54  fof(f134,plain,(
% 1.23/0.54    sK2 != k2_enumset1(sK1,sK1,sK1,sK1) | sK2 != sK3),
% 1.23/0.54    inference(inner_rewriting,[],[f133])).
% 1.23/0.54  fof(f133,plain,(
% 1.23/0.54    sK3 != k2_enumset1(sK1,sK1,sK1,sK1) | sK2 != sK3),
% 1.23/0.54    inference(inner_rewriting,[],[f88])).
% 1.23/0.54  fof(f88,plain,(
% 1.23/0.54    sK3 != k2_enumset1(sK1,sK1,sK1,sK1) | sK2 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.23/0.54    inference(definition_unfolding,[],[f46,f85,f85])).
% 1.23/0.54  fof(f46,plain,(
% 1.23/0.54    sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)),
% 1.23/0.54    inference(cnf_transformation,[],[f27])).
% 1.23/0.54  fof(f132,plain,(
% 1.23/0.54    ~spl7_3 | ~spl7_4),
% 1.23/0.54    inference(avatar_split_clause,[],[f87,f129,f125])).
% 1.23/0.54  fof(f87,plain,(
% 1.23/0.54    sK3 != k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 != sK2),
% 1.23/0.54    inference(definition_unfolding,[],[f47,f85])).
% 1.23/0.54  fof(f47,plain,(
% 1.23/0.54    sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2),
% 1.23/0.54    inference(cnf_transformation,[],[f27])).
% 1.23/0.54  fof(f123,plain,(
% 1.23/0.54    ~spl7_1 | ~spl7_2),
% 1.23/0.54    inference(avatar_split_clause,[],[f86,f120,f116])).
% 1.23/0.54  fof(f86,plain,(
% 1.23/0.54    k1_xboole_0 != sK3 | sK2 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.23/0.54    inference(definition_unfolding,[],[f48,f85])).
% 1.23/0.54  fof(f48,plain,(
% 1.23/0.54    k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)),
% 1.23/0.54    inference(cnf_transformation,[],[f27])).
% 1.23/0.54  % SZS output end Proof for theBenchmark
% 1.23/0.54  % (23500)------------------------------
% 1.23/0.54  % (23500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (23500)Termination reason: Refutation
% 1.23/0.54  
% 1.23/0.54  % (23500)Memory used [KB]: 10874
% 1.23/0.54  % (23500)Time elapsed: 0.113 s
% 1.23/0.54  % (23500)------------------------------
% 1.23/0.54  % (23500)------------------------------
% 1.23/0.54  % (23493)Success in time 0.177 s
%------------------------------------------------------------------------------
