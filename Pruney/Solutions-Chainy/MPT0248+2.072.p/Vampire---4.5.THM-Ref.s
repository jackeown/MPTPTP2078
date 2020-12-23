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
% DateTime   : Thu Dec  3 12:37:59 EST 2020

% Result     : Theorem 2.44s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 734 expanded)
%              Number of leaves         :   30 ( 242 expanded)
%              Depth                    :   16
%              Number of atoms          :  318 (1258 expanded)
%              Number of equality atoms :  131 ( 978 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1589,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f147,f148,f569,f960,f1087,f1584])).

fof(f1584,plain,
    ( ~ spl7_1
    | spl7_2
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f1583])).

fof(f1583,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f1574,f911])).

fof(f911,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,sK2)
    | spl7_2 ),
    inference(forward_demodulation,[],[f910,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f910,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK2,sK2),sK2)
    | spl7_2 ),
    inference(forward_demodulation,[],[f909,f112])).

fof(f112,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f63,f107])).

fof(f107,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f104])).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f90,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f96,f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f97,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f98,f99])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f90,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f909,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK2,sK2),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f852,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f80,f106])).

fof(f106,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f70,f105])).

fof(f105,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f104])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f852,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f125,f125,f137,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f137,plain,
    ( k1_xboole_0 != sK2
    | spl7_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f125,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1574,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2)
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(superposition,[],[f62,f1298])).

fof(f1298,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0))
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(superposition,[],[f91,f1249])).

fof(f1249,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f1239,f167])).

fof(f167,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl7_5
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1239,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl7_1 ),
    inference(superposition,[],[f118,f1148])).

fof(f1148,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f111,f132])).

fof(f132,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f111,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f56,f107,f105])).

fof(f56,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f79,f106])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1087,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f1086])).

fof(f1086,plain,
    ( $false
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f983,f61])).

fof(f61,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f983,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)),k1_xboole_0)
    | ~ spl7_3
    | spl7_4 ),
    inference(backward_demodulation,[],[f200,f141])).

fof(f141,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f200,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f176,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f89,f107])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f176,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f163,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f163,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f149,f146])).

fof(f146,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl7_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f149,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f111,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f105])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f960,plain,
    ( ~ spl7_1
    | spl7_4
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f959])).

fof(f959,plain,
    ( $false
    | ~ spl7_1
    | spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f958,f957])).

fof(f957,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl7_1
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f163,f856])).

fof(f856,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK0,X2)
        | r1_tarski(sK1,X2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f119,f132])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f88,f107])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f958,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl7_1
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f168,f857])).

fof(f857,plain,
    ( ! [X3] :
        ( r1_xboole_0(sK1,X3)
        | r2_hidden(sK0,X3) )
    | ~ spl7_1 ),
    inference(superposition,[],[f115,f132])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f107])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f168,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f569,plain,
    ( spl7_3
    | spl7_1 ),
    inference(avatar_split_clause,[],[f566,f131,f140])).

fof(f566,plain,
    ( k1_xboole_0 = sK1
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f126,f156,f249,f92])).

fof(f249,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f210,f115])).

fof(f210,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f181,f119])).

fof(f181,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f133,f156,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f133,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f156,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f114,f111])).

fof(f114,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f66,f105])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f126,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f148,plain,
    ( ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f110,f144,f131])).

fof(f110,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f57,f107,f107])).

fof(f57,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f147,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f109,f144,f140])).

fof(f109,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f58,f107])).

fof(f58,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f138,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f108,f135,f131])).

fof(f108,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f59,f107])).

fof(f59,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:09:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (32165)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (32157)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (32165)Refutation not found, incomplete strategy% (32165)------------------------------
% 0.21/0.50  % (32165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32165)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32165)Memory used [KB]: 10618
% 0.21/0.50  % (32165)Time elapsed: 0.090 s
% 0.21/0.50  % (32165)------------------------------
% 0.21/0.50  % (32165)------------------------------
% 0.21/0.51  % (32161)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.17/0.51  % (32184)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.17/0.52  % (32159)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.52  % (32169)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.17/0.52  % (32160)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.53  % (32158)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.17/0.53  % (32180)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.17/0.53  % (32170)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.17/0.53  % (32178)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.17/0.53  % (32164)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.17/0.53  % (32179)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.53  % (32176)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.53  % (32177)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.54  % (32156)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.54  % (32181)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.54  % (32168)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.54  % (32162)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (32167)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (32171)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.54  % (32163)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.55  % (32155)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.55  % (32174)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.55  % (32185)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.55  % (32172)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.55  % (32182)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.55  % (32173)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.56  % (32166)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.56  % (32166)Refutation not found, incomplete strategy% (32166)------------------------------
% 1.29/0.56  % (32166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (32166)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (32166)Memory used [KB]: 10618
% 1.29/0.56  % (32166)Time elapsed: 0.149 s
% 1.29/0.56  % (32166)------------------------------
% 1.29/0.56  % (32166)------------------------------
% 1.29/0.56  % (32183)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.57  % (32163)Refutation not found, incomplete strategy% (32163)------------------------------
% 1.29/0.57  % (32163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.57  % (32163)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.57  
% 1.29/0.57  % (32163)Memory used [KB]: 10746
% 1.29/0.57  % (32163)Time elapsed: 0.157 s
% 1.29/0.57  % (32163)------------------------------
% 1.29/0.57  % (32163)------------------------------
% 1.98/0.64  % (32256)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.44/0.71  % (32298)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.44/0.71  % (32291)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.44/0.75  % (32182)Refutation found. Thanks to Tanya!
% 2.44/0.75  % SZS status Theorem for theBenchmark
% 2.44/0.75  % SZS output start Proof for theBenchmark
% 2.44/0.75  fof(f1589,plain,(
% 2.44/0.75    $false),
% 2.44/0.75    inference(avatar_sat_refutation,[],[f138,f147,f148,f569,f960,f1087,f1584])).
% 2.44/0.75  fof(f1584,plain,(
% 2.44/0.75    ~spl7_1 | spl7_2 | ~spl7_5),
% 2.44/0.75    inference(avatar_contradiction_clause,[],[f1583])).
% 2.44/0.75  fof(f1583,plain,(
% 2.44/0.75    $false | (~spl7_1 | spl7_2 | ~spl7_5)),
% 2.44/0.75    inference(subsumption_resolution,[],[f1574,f911])).
% 2.44/0.75  fof(f911,plain,(
% 2.44/0.75    k1_xboole_0 != k5_xboole_0(k1_xboole_0,sK2) | spl7_2),
% 2.44/0.75    inference(forward_demodulation,[],[f910,f62])).
% 2.44/0.75  fof(f62,plain,(
% 2.44/0.75    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f11])).
% 2.44/0.75  fof(f11,axiom,(
% 2.44/0.75    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.44/0.75  fof(f910,plain,(
% 2.44/0.75    k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK2,sK2),sK2) | spl7_2),
% 2.44/0.75    inference(forward_demodulation,[],[f909,f112])).
% 2.44/0.75  fof(f112,plain,(
% 2.44/0.75    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.44/0.75    inference(definition_unfolding,[],[f63,f107])).
% 2.44/0.75  fof(f107,plain,(
% 2.44/0.75    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f64,f104])).
% 2.44/0.75  fof(f104,plain,(
% 2.44/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f69,f103])).
% 2.44/0.75  fof(f103,plain,(
% 2.44/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f90,f102])).
% 2.44/0.75  fof(f102,plain,(
% 2.44/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f96,f101])).
% 2.44/0.75  fof(f101,plain,(
% 2.44/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f97,f100])).
% 2.44/0.75  fof(f100,plain,(
% 2.44/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f98,f99])).
% 2.44/0.75  fof(f99,plain,(
% 2.44/0.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f19])).
% 2.44/0.75  fof(f19,axiom,(
% 2.44/0.75    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.44/0.75  fof(f98,plain,(
% 2.44/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f18])).
% 2.44/0.75  fof(f18,axiom,(
% 2.44/0.75    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.44/0.75  fof(f97,plain,(
% 2.44/0.75    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f17])).
% 2.44/0.75  fof(f17,axiom,(
% 2.44/0.75    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.44/0.75  fof(f96,plain,(
% 2.44/0.75    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f16])).
% 2.44/0.75  fof(f16,axiom,(
% 2.44/0.75    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.44/0.75  fof(f90,plain,(
% 2.44/0.75    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f15])).
% 2.44/0.75  fof(f15,axiom,(
% 2.44/0.75    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.44/0.75  fof(f69,plain,(
% 2.44/0.75    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f14])).
% 2.44/0.75  fof(f14,axiom,(
% 2.44/0.75    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.44/0.75  fof(f64,plain,(
% 2.44/0.75    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f13])).
% 2.44/0.75  fof(f13,axiom,(
% 2.44/0.75    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.44/0.75  fof(f63,plain,(
% 2.44/0.75    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 2.44/0.75    inference(cnf_transformation,[],[f25])).
% 2.44/0.75  fof(f25,axiom,(
% 2.44/0.75    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 2.44/0.75  fof(f909,plain,(
% 2.44/0.75    k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK2,sK2),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | spl7_2),
% 2.44/0.75    inference(unit_resulting_resolution,[],[f852,f117])).
% 2.44/0.75  fof(f117,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.44/0.75    inference(definition_unfolding,[],[f80,f106])).
% 2.44/0.75  fof(f106,plain,(
% 2.44/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.44/0.75    inference(definition_unfolding,[],[f70,f105])).
% 2.44/0.75  fof(f105,plain,(
% 2.44/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.44/0.75    inference(definition_unfolding,[],[f68,f104])).
% 2.44/0.75  fof(f68,plain,(
% 2.44/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.44/0.75    inference(cnf_transformation,[],[f23])).
% 2.44/0.75  fof(f23,axiom,(
% 2.44/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.44/0.75  fof(f70,plain,(
% 2.44/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.44/0.75    inference(cnf_transformation,[],[f12])).
% 2.44/0.75  fof(f12,axiom,(
% 2.44/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.44/0.75  fof(f80,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.44/0.75    inference(cnf_transformation,[],[f46])).
% 2.44/0.75  fof(f46,plain,(
% 2.44/0.75    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.44/0.75    inference(nnf_transformation,[],[f3])).
% 2.44/0.75  fof(f3,axiom,(
% 2.44/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.44/0.75  fof(f852,plain,(
% 2.44/0.75    ~r1_xboole_0(sK2,sK2) | spl7_2),
% 2.44/0.75    inference(unit_resulting_resolution,[],[f125,f125,f137,f92])).
% 2.44/0.75  fof(f92,plain,(
% 2.44/0.75    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f37])).
% 2.44/0.75  fof(f37,plain,(
% 2.44/0.75    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.44/0.75    inference(flattening,[],[f36])).
% 2.44/0.75  fof(f36,plain,(
% 2.44/0.75    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.44/0.75    inference(ennf_transformation,[],[f8])).
% 2.44/0.75  fof(f8,axiom,(
% 2.44/0.75    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 2.44/0.75  fof(f137,plain,(
% 2.44/0.75    k1_xboole_0 != sK2 | spl7_2),
% 2.44/0.75    inference(avatar_component_clause,[],[f135])).
% 2.44/0.75  fof(f135,plain,(
% 2.44/0.75    spl7_2 <=> k1_xboole_0 = sK2),
% 2.44/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.44/0.75  fof(f125,plain,(
% 2.44/0.75    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.44/0.75    inference(equality_resolution,[],[f74])).
% 2.44/0.75  fof(f74,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.44/0.75    inference(cnf_transformation,[],[f41])).
% 2.44/0.75  fof(f41,plain,(
% 2.44/0.75    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.44/0.75    inference(flattening,[],[f40])).
% 2.44/0.75  fof(f40,plain,(
% 2.44/0.75    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.44/0.75    inference(nnf_transformation,[],[f5])).
% 2.44/0.75  fof(f5,axiom,(
% 2.44/0.75    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.44/0.75  fof(f1574,plain,(
% 2.44/0.75    k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2) | (~spl7_1 | ~spl7_5)),
% 2.44/0.75    inference(superposition,[],[f62,f1298])).
% 2.44/0.75  fof(f1298,plain,(
% 2.44/0.75    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0))) ) | (~spl7_1 | ~spl7_5)),
% 2.44/0.75    inference(superposition,[],[f91,f1249])).
% 2.44/0.75  fof(f1249,plain,(
% 2.44/0.75    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | (~spl7_1 | ~spl7_5)),
% 2.44/0.75    inference(subsumption_resolution,[],[f1239,f167])).
% 2.44/0.75  fof(f167,plain,(
% 2.44/0.75    r1_xboole_0(sK1,sK2) | ~spl7_5),
% 2.44/0.75    inference(avatar_component_clause,[],[f166])).
% 2.44/0.75  fof(f166,plain,(
% 2.44/0.75    spl7_5 <=> r1_xboole_0(sK1,sK2)),
% 2.44/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.44/0.75  fof(f1239,plain,(
% 2.44/0.75    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | ~r1_xboole_0(sK1,sK2) | ~spl7_1),
% 2.44/0.75    inference(superposition,[],[f118,f1148])).
% 2.44/0.75  fof(f1148,plain,(
% 2.44/0.75    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl7_1),
% 2.44/0.75    inference(backward_demodulation,[],[f111,f132])).
% 2.44/0.75  fof(f132,plain,(
% 2.44/0.75    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl7_1),
% 2.44/0.75    inference(avatar_component_clause,[],[f131])).
% 2.44/0.75  fof(f131,plain,(
% 2.44/0.75    spl7_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.44/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.44/0.75  fof(f111,plain,(
% 2.44/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.44/0.75    inference(definition_unfolding,[],[f56,f107,f105])).
% 2.44/0.75  fof(f56,plain,(
% 2.44/0.75    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.44/0.75    inference(cnf_transformation,[],[f39])).
% 2.44/0.75  fof(f39,plain,(
% 2.44/0.75    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.44/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f38])).
% 2.44/0.75  fof(f38,plain,(
% 2.44/0.75    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.44/0.75    introduced(choice_axiom,[])).
% 2.44/0.75  fof(f31,plain,(
% 2.44/0.75    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.44/0.75    inference(ennf_transformation,[],[f29])).
% 2.44/0.75  fof(f29,negated_conjecture,(
% 2.44/0.75    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.44/0.75    inference(negated_conjecture,[],[f28])).
% 2.44/0.75  fof(f28,conjecture,(
% 2.44/0.75    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.44/0.75  fof(f118,plain,(
% 2.44/0.75    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f79,f106])).
% 2.44/0.75  fof(f79,plain,(
% 2.44/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f46])).
% 2.44/0.75  fof(f91,plain,(
% 2.44/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.44/0.75    inference(cnf_transformation,[],[f10])).
% 2.44/0.75  fof(f10,axiom,(
% 2.44/0.75    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.44/0.75  fof(f1087,plain,(
% 2.44/0.75    ~spl7_3 | spl7_4),
% 2.44/0.75    inference(avatar_contradiction_clause,[],[f1086])).
% 2.44/0.75  fof(f1086,plain,(
% 2.44/0.75    $false | (~spl7_3 | spl7_4)),
% 2.44/0.75    inference(subsumption_resolution,[],[f983,f61])).
% 2.44/0.75  fof(f61,plain,(
% 2.44/0.75    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f7])).
% 2.44/0.75  fof(f7,axiom,(
% 2.44/0.75    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.44/0.75  fof(f983,plain,(
% 2.44/0.75    ~r1_xboole_0(k6_enumset1(sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2),sK3(k1_xboole_0,sK2)),k1_xboole_0) | (~spl7_3 | spl7_4)),
% 2.44/0.75    inference(backward_demodulation,[],[f200,f141])).
% 2.44/0.75  fof(f141,plain,(
% 2.44/0.75    k1_xboole_0 = sK1 | ~spl7_3),
% 2.44/0.75    inference(avatar_component_clause,[],[f140])).
% 2.44/0.75  fof(f140,plain,(
% 2.44/0.75    spl7_3 <=> k1_xboole_0 = sK1),
% 2.44/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.44/0.75  fof(f200,plain,(
% 2.44/0.75    ~r1_xboole_0(k6_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1) | spl7_4),
% 2.44/0.75    inference(unit_resulting_resolution,[],[f176,f121])).
% 2.44/0.75  fof(f121,plain,(
% 2.44/0.75    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f89,f107])).
% 2.44/0.75  fof(f89,plain,(
% 2.44/0.75    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f35])).
% 2.44/0.75  fof(f35,plain,(
% 2.44/0.75    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.44/0.75    inference(ennf_transformation,[],[f21])).
% 2.44/0.75  fof(f21,axiom,(
% 2.44/0.75    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 2.44/0.75  fof(f176,plain,(
% 2.44/0.75    r2_hidden(sK3(sK1,sK2),sK1) | spl7_4),
% 2.44/0.75    inference(unit_resulting_resolution,[],[f163,f77])).
% 2.44/0.75  fof(f77,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f45])).
% 2.44/0.75  fof(f45,plain,(
% 2.44/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 2.44/0.75  fof(f44,plain,(
% 2.44/0.75    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.44/0.75    introduced(choice_axiom,[])).
% 2.44/0.75  fof(f43,plain,(
% 2.44/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.75    inference(rectify,[],[f42])).
% 2.44/0.75  fof(f42,plain,(
% 2.44/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.75    inference(nnf_transformation,[],[f34])).
% 2.44/0.75  fof(f34,plain,(
% 2.44/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.44/0.75    inference(ennf_transformation,[],[f2])).
% 2.44/0.75  fof(f2,axiom,(
% 2.44/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.44/0.75  fof(f163,plain,(
% 2.44/0.75    ~r1_tarski(sK1,sK2) | spl7_4),
% 2.44/0.75    inference(subsumption_resolution,[],[f149,f146])).
% 2.44/0.75  fof(f146,plain,(
% 2.44/0.75    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl7_4),
% 2.44/0.75    inference(avatar_component_clause,[],[f144])).
% 2.44/0.75  fof(f144,plain,(
% 2.44/0.75    spl7_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.44/0.75    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.44/0.75  fof(f149,plain,(
% 2.44/0.75    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2)),
% 2.44/0.75    inference(superposition,[],[f111,f116])).
% 2.44/0.75  fof(f116,plain,(
% 2.44/0.75    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f72,f105])).
% 2.44/0.75  fof(f72,plain,(
% 2.44/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f33])).
% 2.44/0.75  fof(f33,plain,(
% 2.44/0.75    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.44/0.75    inference(ennf_transformation,[],[f6])).
% 2.44/0.75  fof(f6,axiom,(
% 2.44/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.44/0.75  fof(f960,plain,(
% 2.44/0.75    ~spl7_1 | spl7_4 | spl7_5),
% 2.44/0.75    inference(avatar_contradiction_clause,[],[f959])).
% 2.44/0.75  fof(f959,plain,(
% 2.44/0.75    $false | (~spl7_1 | spl7_4 | spl7_5)),
% 2.44/0.75    inference(subsumption_resolution,[],[f958,f957])).
% 2.44/0.75  fof(f957,plain,(
% 2.44/0.75    ~r2_hidden(sK0,sK2) | (~spl7_1 | spl7_4)),
% 2.44/0.75    inference(unit_resulting_resolution,[],[f163,f856])).
% 2.44/0.75  fof(f856,plain,(
% 2.44/0.75    ( ! [X2] : (~r2_hidden(sK0,X2) | r1_tarski(sK1,X2)) ) | ~spl7_1),
% 2.44/0.75    inference(superposition,[],[f119,f132])).
% 2.44/0.75  fof(f119,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f88,f107])).
% 2.44/0.75  fof(f88,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f53])).
% 2.44/0.75  fof(f53,plain,(
% 2.44/0.75    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.44/0.75    inference(nnf_transformation,[],[f26])).
% 2.44/0.75  fof(f26,axiom,(
% 2.44/0.75    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 2.44/0.75  fof(f958,plain,(
% 2.44/0.75    r2_hidden(sK0,sK2) | (~spl7_1 | spl7_5)),
% 2.44/0.75    inference(unit_resulting_resolution,[],[f168,f857])).
% 2.44/0.75  fof(f857,plain,(
% 2.44/0.75    ( ! [X3] : (r1_xboole_0(sK1,X3) | r2_hidden(sK0,X3)) ) | ~spl7_1),
% 2.44/0.75    inference(superposition,[],[f115,f132])).
% 2.44/0.75  fof(f115,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.44/0.75    inference(definition_unfolding,[],[f71,f107])).
% 2.44/0.75  fof(f71,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f32])).
% 2.44/0.75  fof(f32,plain,(
% 2.44/0.75    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.44/0.75    inference(ennf_transformation,[],[f22])).
% 2.44/0.75  fof(f22,axiom,(
% 2.44/0.75    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.44/0.75  fof(f168,plain,(
% 2.44/0.75    ~r1_xboole_0(sK1,sK2) | spl7_5),
% 2.44/0.75    inference(avatar_component_clause,[],[f166])).
% 2.44/0.75  fof(f569,plain,(
% 2.44/0.75    spl7_3 | spl7_1),
% 2.44/0.75    inference(avatar_split_clause,[],[f566,f131,f140])).
% 2.44/0.75  fof(f566,plain,(
% 2.44/0.75    k1_xboole_0 = sK1 | spl7_1),
% 2.44/0.75    inference(unit_resulting_resolution,[],[f126,f156,f249,f92])).
% 2.44/0.75  fof(f249,plain,(
% 2.44/0.75    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl7_1),
% 2.44/0.75    inference(unit_resulting_resolution,[],[f210,f115])).
% 2.44/0.75  fof(f210,plain,(
% 2.44/0.75    ~r2_hidden(sK0,sK1) | spl7_1),
% 2.44/0.75    inference(unit_resulting_resolution,[],[f181,f119])).
% 2.44/0.75  fof(f181,plain,(
% 2.44/0.75    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl7_1),
% 2.44/0.75    inference(unit_resulting_resolution,[],[f133,f156,f75])).
% 2.44/0.75  fof(f75,plain,(
% 2.44/0.75    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.44/0.75    inference(cnf_transformation,[],[f41])).
% 2.44/0.75  fof(f133,plain,(
% 2.44/0.75    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl7_1),
% 2.44/0.75    inference(avatar_component_clause,[],[f131])).
% 2.44/0.75  fof(f156,plain,(
% 2.44/0.75    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.44/0.75    inference(superposition,[],[f114,f111])).
% 2.44/0.75  fof(f114,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.44/0.75    inference(definition_unfolding,[],[f66,f105])).
% 2.44/0.75  fof(f66,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.44/0.75    inference(cnf_transformation,[],[f9])).
% 2.44/0.75  fof(f9,axiom,(
% 2.44/0.75    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.44/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.44/0.75  fof(f126,plain,(
% 2.44/0.75    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.44/0.75    inference(equality_resolution,[],[f73])).
% 2.44/0.75  fof(f73,plain,(
% 2.44/0.75    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.44/0.75    inference(cnf_transformation,[],[f41])).
% 2.44/0.75  fof(f148,plain,(
% 2.44/0.75    ~spl7_1 | ~spl7_4),
% 2.44/0.75    inference(avatar_split_clause,[],[f110,f144,f131])).
% 2.44/0.75  fof(f110,plain,(
% 2.44/0.75    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.44/0.75    inference(definition_unfolding,[],[f57,f107,f107])).
% 2.44/0.75  fof(f57,plain,(
% 2.44/0.75    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.44/0.75    inference(cnf_transformation,[],[f39])).
% 2.44/0.75  fof(f147,plain,(
% 2.44/0.75    ~spl7_3 | ~spl7_4),
% 2.44/0.75    inference(avatar_split_clause,[],[f109,f144,f140])).
% 2.44/0.75  fof(f109,plain,(
% 2.44/0.75    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.44/0.75    inference(definition_unfolding,[],[f58,f107])).
% 2.44/0.75  fof(f58,plain,(
% 2.44/0.75    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.44/0.75    inference(cnf_transformation,[],[f39])).
% 2.44/0.75  fof(f138,plain,(
% 2.44/0.75    ~spl7_1 | ~spl7_2),
% 2.44/0.75    inference(avatar_split_clause,[],[f108,f135,f131])).
% 2.44/0.75  fof(f108,plain,(
% 2.44/0.75    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.44/0.75    inference(definition_unfolding,[],[f59,f107])).
% 2.44/0.75  fof(f59,plain,(
% 2.44/0.75    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 2.44/0.75    inference(cnf_transformation,[],[f39])).
% 2.44/0.75  % SZS output end Proof for theBenchmark
% 2.44/0.75  % (32182)------------------------------
% 2.44/0.75  % (32182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.44/0.75  % (32182)Termination reason: Refutation
% 2.44/0.75  
% 2.44/0.75  % (32182)Memory used [KB]: 12537
% 2.44/0.75  % (32182)Time elapsed: 0.332 s
% 2.44/0.75  % (32182)------------------------------
% 2.44/0.75  % (32182)------------------------------
% 2.44/0.76  % (32150)Success in time 0.394 s
%------------------------------------------------------------------------------
