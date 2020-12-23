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
% DateTime   : Thu Dec  3 12:41:00 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 357 expanded)
%              Number of leaves         :   20 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  264 (1178 expanded)
%              Number of equality atoms :   79 ( 272 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f102,f1083,f1208])).

fof(f1208,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f1207])).

fof(f1207,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f1203,f100])).

fof(f100,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1203,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl7_1 ),
    inference(trivial_inequality_removal,[],[f1173])).

fof(f1173,plain,
    ( sK3 != sK3
    | ~ r2_hidden(sK2,sK3)
    | ~ spl7_1 ),
    inference(superposition,[],[f86,f1147])).

fof(f1147,plain,
    ( sK3 = k4_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f1146,f423])).

fof(f423,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f120,f410])).

fof(f410,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f402])).

fof(f402,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f111,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k4_xboole_0(X0,X1)),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f108,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

% (10507)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f68,f92])).

fof(f92,plain,(
    ! [X0,X1] : sP1(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X0,X1)),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f110,f47])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f69,f92])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f120,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f80,f112])).

fof(f112,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(resolution,[],[f84,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

% (10516)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f52,f51])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1146,plain,
    ( k4_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k1_xboole_0)
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f1122,f410])).

fof(f1122,plain,
    ( k4_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | ~ spl7_1 ),
    inference(superposition,[],[f127,f95])).

fof(f95,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl7_1
  <=> k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f127,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f80,f83])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f49,f51,f51])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f57,f79])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f1083,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f1082])).

fof(f1082,plain,
    ( $false
    | spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f1081,f167])).

fof(f167,plain,
    ( ~ r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f165,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f165,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3))
    | spl7_1 ),
    inference(extensionality_resolution,[],[f56,f96])).

fof(f96,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK2) != k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1081,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3))
    | spl7_2 ),
    inference(forward_demodulation,[],[f1080,f425])).

fof(f425,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f112,f410])).

fof(f1080,plain,
    ( r1_tarski(k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3))
    | spl7_2 ),
    inference(forward_demodulation,[],[f1060,f410])).

fof(f1060,plain,
    ( r1_tarski(k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k4_xboole_0(sK3,sK3)),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3))
    | spl7_2 ),
    inference(superposition,[],[f146,f207])).

fof(f207,plain,
    ( sK3 = k4_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl7_2 ),
    inference(resolution,[],[f85,f99])).

% (10511)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f99,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f146,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f129,f83])).

fof(f129,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5) ),
    inference(superposition,[],[f48,f83])).

fof(f102,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f82,f98,f94])).

fof(f82,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f44,f79,f79])).

fof(f44,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( r2_hidden(sK2,sK3)
      | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3) )
    & ( ~ r2_hidden(sK2,sK3)
      | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK2,sK3)
        | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3) )
      & ( ~ r2_hidden(sK2,sK3)
        | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f15])).

% (10510)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f15,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f101,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f81,f98,f94])).

fof(f81,plain,
    ( r2_hidden(sK2,sK3)
    | k3_enumset1(sK2,sK2,sK2,sK2,sK2) != k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f45,f79,f79])).

fof(f45,plain,
    ( r2_hidden(sK2,sK3)
    | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:54:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (10505)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (10503)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (10513)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (10521)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.48/0.57  % (10504)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.48/0.57  % (10522)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.48/0.57  % (10501)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.48/0.57  % (10514)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.57  % (10502)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.48/0.58  % (10527)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.48/0.58  % (10499)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.48/0.58  % (10500)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.48/0.58  % (10506)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.58  % (10519)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.79/0.59  % (10520)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.79/0.60  % (10524)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.79/0.60  % (10515)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.79/0.60  % (10527)Refutation not found, incomplete strategy% (10527)------------------------------
% 1.79/0.60  % (10527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (10527)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.60  
% 1.79/0.60  % (10527)Memory used [KB]: 10746
% 1.79/0.60  % (10527)Time elapsed: 0.178 s
% 1.79/0.60  % (10527)------------------------------
% 1.79/0.60  % (10527)------------------------------
% 1.79/0.60  % (10528)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.79/0.60  % (10515)Refutation not found, incomplete strategy% (10515)------------------------------
% 1.79/0.60  % (10515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (10515)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.60  
% 1.79/0.60  % (10515)Memory used [KB]: 10618
% 1.79/0.60  % (10515)Time elapsed: 0.173 s
% 1.79/0.60  % (10515)------------------------------
% 1.79/0.60  % (10515)------------------------------
% 1.79/0.60  % (10528)Refutation not found, incomplete strategy% (10528)------------------------------
% 1.79/0.60  % (10528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (10528)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.60  
% 1.79/0.60  % (10528)Memory used [KB]: 1663
% 1.79/0.60  % (10528)Time elapsed: 0.002 s
% 1.79/0.60  % (10528)------------------------------
% 1.79/0.60  % (10528)------------------------------
% 1.79/0.60  % (10525)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.79/0.61  % (10526)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.79/0.61  % (10523)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.79/0.61  % (10517)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.79/0.61  % (10505)Refutation found. Thanks to Tanya!
% 1.79/0.61  % SZS status Theorem for theBenchmark
% 1.79/0.61  % (10512)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.79/0.61  % (10518)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.79/0.61  % SZS output start Proof for theBenchmark
% 1.79/0.61  fof(f1232,plain,(
% 1.79/0.61    $false),
% 1.79/0.61    inference(avatar_sat_refutation,[],[f101,f102,f1083,f1208])).
% 1.79/0.61  fof(f1208,plain,(
% 1.79/0.61    ~spl7_1 | ~spl7_2),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f1207])).
% 1.79/0.61  fof(f1207,plain,(
% 1.79/0.61    $false | (~spl7_1 | ~spl7_2)),
% 1.79/0.61    inference(subsumption_resolution,[],[f1203,f100])).
% 1.79/0.61  fof(f100,plain,(
% 1.79/0.61    r2_hidden(sK2,sK3) | ~spl7_2),
% 1.79/0.61    inference(avatar_component_clause,[],[f98])).
% 1.79/0.61  fof(f98,plain,(
% 1.79/0.61    spl7_2 <=> r2_hidden(sK2,sK3)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.79/0.61  fof(f1203,plain,(
% 1.79/0.61    ~r2_hidden(sK2,sK3) | ~spl7_1),
% 1.79/0.61    inference(trivial_inequality_removal,[],[f1173])).
% 1.79/0.61  fof(f1173,plain,(
% 1.79/0.61    sK3 != sK3 | ~r2_hidden(sK2,sK3) | ~spl7_1),
% 1.79/0.61    inference(superposition,[],[f86,f1147])).
% 1.79/0.61  fof(f1147,plain,(
% 1.79/0.61    sK3 = k4_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~spl7_1),
% 1.79/0.61    inference(forward_demodulation,[],[f1146,f423])).
% 1.79/0.61  fof(f423,plain,(
% 1.79/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.79/0.61    inference(backward_demodulation,[],[f120,f410])).
% 1.79/0.61  fof(f410,plain,(
% 1.79/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.79/0.61    inference(duplicate_literal_removal,[],[f402])).
% 1.79/0.61  fof(f402,plain,(
% 1.79/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.79/0.61    inference(resolution,[],[f111,f109])).
% 1.79/0.61  fof(f109,plain,(
% 1.79/0.61    ( ! [X0,X1] : (r2_hidden(sK4(k4_xboole_0(X0,X1)),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.79/0.61    inference(resolution,[],[f108,f47])).
% 1.79/0.61  fof(f47,plain,(
% 1.79/0.61    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.79/0.61    inference(cnf_transformation,[],[f28])).
% 1.79/0.61  fof(f28,plain,(
% 1.79/0.61    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f27])).
% 1.79/0.61  fof(f27,plain,(
% 1.79/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f18,plain,(
% 1.79/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.79/0.61    inference(ennf_transformation,[],[f4])).
% 1.79/0.61  % (10507)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.79/0.61  fof(f4,axiom,(
% 1.79/0.61    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.79/0.61  fof(f108,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 1.79/0.61    inference(resolution,[],[f68,f92])).
% 1.79/0.61  fof(f92,plain,(
% 1.79/0.61    ( ! [X0,X1] : (sP1(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.79/0.61    inference(equality_resolution,[],[f74])).
% 1.79/0.61  fof(f74,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.79/0.61    inference(cnf_transformation,[],[f43])).
% 1.79/0.61  fof(f43,plain,(
% 1.79/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.61    inference(nnf_transformation,[],[f23])).
% 1.79/0.61  fof(f23,plain,(
% 1.79/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.79/0.61    inference(definition_folding,[],[f3,f22])).
% 1.79/0.61  fof(f22,plain,(
% 1.79/0.61    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.79/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.79/0.61  fof(f3,axiom,(
% 1.79/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.79/0.61  fof(f68,plain,(
% 1.79/0.61    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f42])).
% 1.79/0.61  fof(f42,plain,(
% 1.79/0.61    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f41])).
% 1.79/0.61  fof(f41,plain,(
% 1.79/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f40,plain,(
% 1.79/0.61    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.79/0.61    inference(rectify,[],[f39])).
% 1.79/0.61  fof(f39,plain,(
% 1.79/0.61    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.79/0.61    inference(flattening,[],[f38])).
% 1.79/0.61  fof(f38,plain,(
% 1.79/0.61    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.79/0.61    inference(nnf_transformation,[],[f22])).
% 1.79/0.61  fof(f111,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~r2_hidden(sK4(k4_xboole_0(X0,X1)),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.79/0.61    inference(resolution,[],[f110,f47])).
% 1.79/0.61  fof(f110,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 1.79/0.61    inference(resolution,[],[f69,f92])).
% 1.79/0.61  fof(f69,plain,(
% 1.79/0.61    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f42])).
% 1.79/0.61  fof(f120,plain,(
% 1.79/0.61    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.79/0.61    inference(superposition,[],[f80,f112])).
% 1.79/0.61  fof(f112,plain,(
% 1.79/0.61    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.79/0.61    inference(resolution,[],[f84,f89])).
% 1.79/0.61  fof(f89,plain,(
% 1.79/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.79/0.61    inference(equality_resolution,[],[f55])).
% 1.79/0.61  fof(f55,plain,(
% 1.79/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.79/0.61    inference(cnf_transformation,[],[f30])).
% 1.79/0.61  fof(f30,plain,(
% 1.79/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.79/0.61    inference(flattening,[],[f29])).
% 1.79/0.61  fof(f29,plain,(
% 1.79/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.79/0.61    inference(nnf_transformation,[],[f5])).
% 1.79/0.61  fof(f5,axiom,(
% 1.79/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.79/0.61  % (10516)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.79/0.61  fof(f84,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.79/0.61    inference(definition_unfolding,[],[f53,f51])).
% 1.79/0.61  fof(f51,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.79/0.61    inference(cnf_transformation,[],[f9])).
% 1.79/0.61  fof(f9,axiom,(
% 1.79/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.79/0.61  fof(f53,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f19])).
% 1.79/0.61  fof(f19,plain,(
% 1.79/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.79/0.61    inference(ennf_transformation,[],[f7])).
% 1.79/0.61  fof(f7,axiom,(
% 1.79/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.79/0.61  fof(f80,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.79/0.61    inference(definition_unfolding,[],[f52,f51])).
% 1.79/0.61  fof(f52,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.79/0.61    inference(cnf_transformation,[],[f6])).
% 1.79/0.61  fof(f6,axiom,(
% 1.79/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.79/0.61  fof(f1146,plain,(
% 1.79/0.61    k4_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k1_xboole_0) | ~spl7_1),
% 1.79/0.61    inference(forward_demodulation,[],[f1122,f410])).
% 1.79/0.61  fof(f1122,plain,(
% 1.79/0.61    k4_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) | ~spl7_1),
% 1.79/0.61    inference(superposition,[],[f127,f95])).
% 1.79/0.61  fof(f95,plain,(
% 1.79/0.61    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) | ~spl7_1),
% 1.79/0.61    inference(avatar_component_clause,[],[f94])).
% 1.79/0.61  fof(f94,plain,(
% 1.79/0.61    spl7_1 <=> k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.79/0.61  fof(f127,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.79/0.61    inference(superposition,[],[f80,f83])).
% 1.79/0.61  fof(f83,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.79/0.61    inference(definition_unfolding,[],[f49,f51,f51])).
% 1.79/0.61  fof(f49,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f1])).
% 1.79/0.61  fof(f1,axiom,(
% 1.79/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.79/0.61  fof(f86,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.79/0.61    inference(definition_unfolding,[],[f57,f79])).
% 1.79/0.61  fof(f79,plain,(
% 1.79/0.61    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.79/0.61    inference(definition_unfolding,[],[f46,f78])).
% 1.79/0.61  fof(f78,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.79/0.61    inference(definition_unfolding,[],[f50,f77])).
% 1.79/0.61  fof(f77,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.79/0.61    inference(definition_unfolding,[],[f59,f76])).
% 1.79/0.61  fof(f76,plain,(
% 1.79/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f13])).
% 1.79/0.61  fof(f13,axiom,(
% 1.79/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.79/0.61  fof(f59,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f12])).
% 1.79/0.61  fof(f12,axiom,(
% 1.79/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.79/0.61  fof(f50,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f11])).
% 1.79/0.61  fof(f11,axiom,(
% 1.79/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.79/0.61  fof(f46,plain,(
% 1.79/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f10])).
% 1.79/0.61  fof(f10,axiom,(
% 1.79/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.79/0.61  fof(f57,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.79/0.61    inference(cnf_transformation,[],[f31])).
% 1.79/0.61  fof(f31,plain,(
% 1.79/0.61    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.79/0.61    inference(nnf_transformation,[],[f14])).
% 1.79/0.61  fof(f14,axiom,(
% 1.79/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.79/0.61  fof(f1083,plain,(
% 1.79/0.61    spl7_1 | spl7_2),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f1082])).
% 1.79/0.61  fof(f1082,plain,(
% 1.79/0.61    $false | (spl7_1 | spl7_2)),
% 1.79/0.61    inference(subsumption_resolution,[],[f1081,f167])).
% 1.79/0.61  fof(f167,plain,(
% 1.79/0.61    ~r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) | spl7_1),
% 1.79/0.61    inference(subsumption_resolution,[],[f165,f48])).
% 1.79/0.61  fof(f48,plain,(
% 1.79/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f8])).
% 1.79/0.61  fof(f8,axiom,(
% 1.79/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.79/0.61  fof(f165,plain,(
% 1.79/0.61    ~r1_tarski(k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) | spl7_1),
% 1.79/0.61    inference(extensionality_resolution,[],[f56,f96])).
% 1.79/0.61  fof(f96,plain,(
% 1.79/0.61    k3_enumset1(sK2,sK2,sK2,sK2,sK2) != k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) | spl7_1),
% 1.79/0.61    inference(avatar_component_clause,[],[f94])).
% 1.79/0.61  fof(f56,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f30])).
% 1.79/0.61  fof(f1081,plain,(
% 1.79/0.61    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) | spl7_2),
% 1.79/0.61    inference(forward_demodulation,[],[f1080,f425])).
% 1.79/0.61  fof(f425,plain,(
% 1.79/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.79/0.61    inference(backward_demodulation,[],[f112,f410])).
% 1.79/0.61  fof(f1080,plain,(
% 1.79/0.61    r1_tarski(k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) | spl7_2),
% 1.79/0.61    inference(forward_demodulation,[],[f1060,f410])).
% 1.79/0.61  fof(f1060,plain,(
% 1.79/0.61    r1_tarski(k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k4_xboole_0(sK3,sK3)),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) | spl7_2),
% 1.79/0.61    inference(superposition,[],[f146,f207])).
% 1.79/0.61  fof(f207,plain,(
% 1.79/0.61    sK3 = k4_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl7_2),
% 1.79/0.61    inference(resolution,[],[f85,f99])).
% 1.79/0.62  % (10511)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.79/0.62  fof(f99,plain,(
% 1.79/0.62    ~r2_hidden(sK2,sK3) | spl7_2),
% 1.79/0.62    inference(avatar_component_clause,[],[f98])).
% 1.79/0.62  fof(f85,plain,(
% 1.79/0.62    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0) )),
% 1.79/0.62    inference(definition_unfolding,[],[f58,f79])).
% 1.79/0.62  fof(f58,plain,(
% 1.79/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f31])).
% 1.79/0.62  fof(f146,plain,(
% 1.79/0.62    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X1,X2))) )),
% 1.79/0.62    inference(superposition,[],[f129,f83])).
% 1.79/0.62  fof(f129,plain,(
% 1.79/0.62    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5)) )),
% 1.79/0.62    inference(superposition,[],[f48,f83])).
% 1.79/0.62  fof(f102,plain,(
% 1.79/0.62    spl7_1 | ~spl7_2),
% 1.79/0.62    inference(avatar_split_clause,[],[f82,f98,f94])).
% 1.79/0.62  fof(f82,plain,(
% 1.79/0.62    ~r2_hidden(sK2,sK3) | k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),
% 1.79/0.62    inference(definition_unfolding,[],[f44,f79,f79])).
% 1.79/0.62  fof(f44,plain,(
% 1.79/0.62    ~r2_hidden(sK2,sK3) | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)),
% 1.79/0.62    inference(cnf_transformation,[],[f26])).
% 1.79/0.62  fof(f26,plain,(
% 1.79/0.62    (r2_hidden(sK2,sK3) | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3)) & (~r2_hidden(sK2,sK3) | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3))),
% 1.79/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).
% 1.79/0.62  fof(f25,plain,(
% 1.79/0.62    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK2,sK3) | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3)) & (~r2_hidden(sK2,sK3) | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)))),
% 1.79/0.62    introduced(choice_axiom,[])).
% 1.79/0.62  fof(f24,plain,(
% 1.79/0.62    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.79/0.62    inference(nnf_transformation,[],[f17])).
% 1.79/0.62  fof(f17,plain,(
% 1.79/0.62    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.79/0.62    inference(ennf_transformation,[],[f16])).
% 1.79/0.62  fof(f16,negated_conjecture,(
% 1.79/0.62    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.79/0.62    inference(negated_conjecture,[],[f15])).
% 1.79/0.62  % (10510)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.79/0.62  fof(f15,conjecture,(
% 1.79/0.62    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.79/0.62  fof(f101,plain,(
% 1.79/0.62    ~spl7_1 | spl7_2),
% 1.79/0.62    inference(avatar_split_clause,[],[f81,f98,f94])).
% 1.79/0.62  fof(f81,plain,(
% 1.79/0.62    r2_hidden(sK2,sK3) | k3_enumset1(sK2,sK2,sK2,sK2,sK2) != k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),
% 1.79/0.62    inference(definition_unfolding,[],[f45,f79,f79])).
% 1.79/0.62  fof(f45,plain,(
% 1.79/0.62    r2_hidden(sK2,sK3) | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3)),
% 1.79/0.62    inference(cnf_transformation,[],[f26])).
% 1.79/0.62  % SZS output end Proof for theBenchmark
% 1.79/0.62  % (10505)------------------------------
% 1.79/0.62  % (10505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.62  % (10505)Termination reason: Refutation
% 1.79/0.62  
% 1.79/0.62  % (10505)Memory used [KB]: 11385
% 1.79/0.62  % (10505)Time elapsed: 0.182 s
% 1.79/0.62  % (10505)------------------------------
% 1.79/0.62  % (10505)------------------------------
% 1.79/0.62  % (10498)Success in time 0.253 s
%------------------------------------------------------------------------------
