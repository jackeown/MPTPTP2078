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
% DateTime   : Thu Dec  3 12:43:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 192 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  216 ( 451 expanded)
%              Number of equality atoms :   42 ( 122 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2015,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f190,f1448,f1453,f1513,f1541,f1973,f2014])).

fof(f2014,plain,
    ( ~ spl5_27
    | spl5_35 ),
    inference(avatar_contradiction_clause,[],[f2010])).

fof(f2010,plain,
    ( $false
    | ~ spl5_27
    | spl5_35 ),
    inference(resolution,[],[f1980,f1446])).

fof(f1446,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f1445,plain,
    ( spl5_27
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f1980,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_35 ),
    inference(trivial_inequality_removal,[],[f1978])).

fof(f1978,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK1,sK2)
    | spl5_35 ),
    inference(superposition,[],[f1540,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f1540,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | spl5_35 ),
    inference(avatar_component_clause,[],[f1538])).

fof(f1538,plain,
    ( spl5_35
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f1973,plain,(
    spl5_27 ),
    inference(avatar_contradiction_clause,[],[f1969])).

fof(f1969,plain,
    ( $false
    | spl5_27 ),
    inference(resolution,[],[f1793,f29])).

fof(f29,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f22])).

fof(f22,plain,
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

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f1793,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl5_27 ),
    inference(resolution,[],[f1447,f161])).

fof(f161,plain,(
    ! [X8,X9] :
      ( r1_xboole_0(X8,X9)
      | ~ r1_xboole_0(X9,X8) ) ),
    inference(trivial_inequality_removal,[],[f156])).

fof(f156,plain,(
    ! [X8,X9] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X8,X9)
      | ~ r1_xboole_0(X9,X8) ) ),
    inference(superposition,[],[f42,f68])).

fof(f68,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k3_xboole_0(X5,X4)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f41,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1447,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f1541,plain,
    ( ~ spl5_7
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f859,f1538,f163])).

fof(f163,plain,
    ( spl5_7
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f859,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f139,f167])).

fof(f167,plain,(
    ~ r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) ),
    inference(resolution,[],[f161,f49])).

fof(f49,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f30,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f139,plain,(
    ! [X14,X12,X13] :
      ( r1_xboole_0(X12,k3_tarski(k2_enumset1(X13,X13,X13,X14)))
      | k1_xboole_0 != k3_xboole_0(X12,X14)
      | ~ r1_xboole_0(X12,X13) ) ),
    inference(superposition,[],[f42,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f1513,plain,
    ( spl5_7
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f1512])).

fof(f1512,plain,
    ( $false
    | spl5_7
    | ~ spl5_8 ),
    inference(resolution,[],[f1492,f165])).

fof(f165,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f163])).

fof(f1492,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_8 ),
    inference(trivial_inequality_removal,[],[f1477])).

fof(f1477,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK0)
    | ~ spl5_8 ),
    inference(superposition,[],[f85,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl5_8
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f85,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k3_xboole_0(X5,X4)
      | r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f42,f33])).

fof(f1453,plain,(
    spl5_26 ),
    inference(avatar_contradiction_clause,[],[f1449])).

fof(f1449,plain,
    ( $false
    | spl5_26 ),
    inference(resolution,[],[f1442,f31])).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1442,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | spl5_26 ),
    inference(avatar_component_clause,[],[f1440])).

fof(f1440,plain,
    ( spl5_26
  <=> r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1448,plain,
    ( ~ spl5_27
    | ~ spl5_26
    | spl5_9 ),
    inference(avatar_split_clause,[],[f1437,f187,f1440,f1445])).

fof(f187,plain,
    ( spl5_9
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1437,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | ~ r1_xboole_0(sK1,sK2)
    | spl5_9 ),
    inference(superposition,[],[f1171,f41])).

fof(f1171,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl5_9 ),
    inference(resolution,[],[f639,f209])).

fof(f209,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl5_9 ),
    inference(resolution,[],[f203,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f38,f28])).

fof(f28,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f203,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | spl5_9 ),
    inference(resolution,[],[f197,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f197,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | spl5_9 ),
    inference(resolution,[],[f189,f161])).

fof(f189,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f187])).

fof(f639,plain,(
    ! [X23,X21,X22] :
      ( r1_xboole_0(k3_xboole_0(X21,X22),X23)
      | ~ r1_xboole_0(X21,k3_xboole_0(X22,X23)) ) ),
    inference(trivial_inequality_removal,[],[f633])).

fof(f633,plain,(
    ! [X23,X21,X22] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k3_xboole_0(X21,X22),X23)
      | ~ r1_xboole_0(X21,k3_xboole_0(X22,X23)) ) ),
    inference(superposition,[],[f125,f41])).

fof(f125,plain,(
    ! [X14,X12,X13] :
      ( k1_xboole_0 != k3_xboole_0(X12,k3_xboole_0(X13,X14))
      | r1_xboole_0(k3_xboole_0(X12,X13),X14) ) ),
    inference(superposition,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f190,plain,
    ( spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f181,f187,f183])).

fof(f181,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f67,f50])).

fof(f50,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f27,f48])).

fof(f27,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 20:59:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (25235)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.44  % (25239)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.45  % (25229)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (25224)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (25221)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (25234)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (25223)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (25228)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (25236)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (25220)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (25226)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (25237)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (25240)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (25238)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (25222)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (25233)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (25232)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (25230)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.54  % (25224)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f2015,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f190,f1448,f1453,f1513,f1541,f1973,f2014])).
% 0.20/0.54  fof(f2014,plain,(
% 0.20/0.54    ~spl5_27 | spl5_35),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f2010])).
% 0.20/0.54  fof(f2010,plain,(
% 0.20/0.54    $false | (~spl5_27 | spl5_35)),
% 0.20/0.54    inference(resolution,[],[f1980,f1446])).
% 0.20/0.54  fof(f1446,plain,(
% 0.20/0.54    r1_xboole_0(sK1,sK2) | ~spl5_27),
% 0.20/0.54    inference(avatar_component_clause,[],[f1445])).
% 0.20/0.54  fof(f1445,plain,(
% 0.20/0.54    spl5_27 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.20/0.54  fof(f1980,plain,(
% 0.20/0.54    ~r1_xboole_0(sK1,sK2) | spl5_35),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f1978])).
% 0.20/0.54  fof(f1978,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK1,sK2) | spl5_35),
% 0.20/0.54    inference(superposition,[],[f1540,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.54  fof(f1540,plain,(
% 0.20/0.54    k1_xboole_0 != k3_xboole_0(sK1,sK2) | spl5_35),
% 0.20/0.54    inference(avatar_component_clause,[],[f1538])).
% 0.20/0.54  fof(f1538,plain,(
% 0.20/0.54    spl5_35 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.20/0.54  fof(f1973,plain,(
% 0.20/0.54    spl5_27),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1969])).
% 0.20/0.54  fof(f1969,plain,(
% 0.20/0.54    $false | spl5_27),
% 0.20/0.54    inference(resolution,[],[f1793,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    r1_xboole_0(sK2,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.20/0.54    inference(flattening,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.54    inference(negated_conjecture,[],[f13])).
% 0.20/0.54  fof(f13,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.20/0.54  fof(f1793,plain,(
% 0.20/0.54    ~r1_xboole_0(sK2,sK1) | spl5_27),
% 0.20/0.54    inference(resolution,[],[f1447,f161])).
% 0.20/0.54  fof(f161,plain,(
% 0.20/0.54    ( ! [X8,X9] : (r1_xboole_0(X8,X9) | ~r1_xboole_0(X9,X8)) )),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f156])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    ( ! [X8,X9] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X8,X9) | ~r1_xboole_0(X9,X8)) )),
% 0.20/0.54    inference(superposition,[],[f42,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X5,X4) | ~r1_xboole_0(X4,X5)) )),
% 0.20/0.54    inference(superposition,[],[f41,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f1447,plain,(
% 0.20/0.54    ~r1_xboole_0(sK1,sK2) | spl5_27),
% 0.20/0.54    inference(avatar_component_clause,[],[f1445])).
% 0.20/0.54  fof(f1541,plain,(
% 0.20/0.54    ~spl5_7 | ~spl5_35),
% 0.20/0.54    inference(avatar_split_clause,[],[f859,f1538,f163])).
% 0.20/0.54  fof(f163,plain,(
% 0.20/0.54    spl5_7 <=> r1_xboole_0(sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.54  fof(f859,plain,(
% 0.20/0.54    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 0.20/0.54    inference(resolution,[],[f139,f167])).
% 0.20/0.54  fof(f167,plain,(
% 0.20/0.54    ~r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))),
% 0.20/0.54    inference(resolution,[],[f161,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 0.20/0.54    inference(definition_unfolding,[],[f30,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f34,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f35,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f139,plain,(
% 0.20/0.54    ( ! [X14,X12,X13] : (r1_xboole_0(X12,k3_tarski(k2_enumset1(X13,X13,X13,X14))) | k1_xboole_0 != k3_xboole_0(X12,X14) | ~r1_xboole_0(X12,X13)) )),
% 0.20/0.54    inference(superposition,[],[f42,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f45,f47])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.20/0.54  fof(f1513,plain,(
% 0.20/0.54    spl5_7 | ~spl5_8),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1512])).
% 0.20/0.54  fof(f1512,plain,(
% 0.20/0.54    $false | (spl5_7 | ~spl5_8)),
% 0.20/0.54    inference(resolution,[],[f1492,f165])).
% 0.20/0.54  fof(f165,plain,(
% 0.20/0.54    ~r1_xboole_0(sK1,sK0) | spl5_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f163])).
% 0.20/0.54  fof(f1492,plain,(
% 0.20/0.54    r1_xboole_0(sK1,sK0) | ~spl5_8),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f1477])).
% 0.20/0.54  fof(f1477,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK0) | ~spl5_8),
% 0.20/0.54    inference(superposition,[],[f85,f185])).
% 0.20/0.54  fof(f185,plain,(
% 0.20/0.54    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl5_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f183])).
% 0.20/0.54  fof(f183,plain,(
% 0.20/0.54    spl5_8 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X4,X5] : (k1_xboole_0 != k3_xboole_0(X5,X4) | r1_xboole_0(X4,X5)) )),
% 0.20/0.54    inference(superposition,[],[f42,f33])).
% 0.20/0.54  fof(f1453,plain,(
% 0.20/0.54    spl5_26),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1449])).
% 0.20/0.54  fof(f1449,plain,(
% 0.20/0.54    $false | spl5_26),
% 0.20/0.54    inference(resolution,[],[f1442,f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.54  fof(f1442,plain,(
% 0.20/0.54    ~r1_xboole_0(sK0,k1_xboole_0) | spl5_26),
% 0.20/0.54    inference(avatar_component_clause,[],[f1440])).
% 0.20/0.54  fof(f1440,plain,(
% 0.20/0.54    spl5_26 <=> r1_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.20/0.54  fof(f1448,plain,(
% 0.20/0.54    ~spl5_27 | ~spl5_26 | spl5_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f1437,f187,f1440,f1445])).
% 0.20/0.54  fof(f187,plain,(
% 0.20/0.54    spl5_9 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.54  fof(f1437,plain,(
% 0.20/0.54    ~r1_xboole_0(sK0,k1_xboole_0) | ~r1_xboole_0(sK1,sK2) | spl5_9),
% 0.20/0.54    inference(superposition,[],[f1171,f41])).
% 0.20/0.54  fof(f1171,plain,(
% 0.20/0.54    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl5_9),
% 0.20/0.54    inference(resolution,[],[f639,f209])).
% 0.20/0.54  fof(f209,plain,(
% 0.20/0.54    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl5_9),
% 0.20/0.54    inference(resolution,[],[f203,f106])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 0.20/0.54    inference(resolution,[],[f38,f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    r2_hidden(sK3,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.54  fof(f203,plain,(
% 0.20/0.54    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | spl5_9),
% 0.20/0.54    inference(resolution,[],[f197,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f39,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f32,f46])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.54  fof(f197,plain,(
% 0.20/0.54    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | spl5_9),
% 0.20/0.54    inference(resolution,[],[f189,f161])).
% 0.20/0.54  fof(f189,plain,(
% 0.20/0.54    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | spl5_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f187])).
% 0.20/0.54  fof(f639,plain,(
% 0.20/0.54    ( ! [X23,X21,X22] : (r1_xboole_0(k3_xboole_0(X21,X22),X23) | ~r1_xboole_0(X21,k3_xboole_0(X22,X23))) )),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f633])).
% 0.20/0.54  fof(f633,plain,(
% 0.20/0.54    ( ! [X23,X21,X22] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k3_xboole_0(X21,X22),X23) | ~r1_xboole_0(X21,k3_xboole_0(X22,X23))) )),
% 0.20/0.54    inference(superposition,[],[f125,f41])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    ( ! [X14,X12,X13] : (k1_xboole_0 != k3_xboole_0(X12,k3_xboole_0(X13,X14)) | r1_xboole_0(k3_xboole_0(X12,X13),X14)) )),
% 0.20/0.54    inference(superposition,[],[f42,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.54  fof(f190,plain,(
% 0.20/0.54    spl5_8 | ~spl5_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f181,f187,f183])).
% 0.20/0.54  fof(f181,plain,(
% 0.20/0.54    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.54    inference(resolution,[],[f67,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.20/0.54    inference(definition_unfolding,[],[f27,f48])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3) | k1_xboole_0 = X2) )),
% 0.20/0.54    inference(superposition,[],[f41,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (25224)------------------------------
% 0.20/0.54  % (25224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25224)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (25224)Memory used [KB]: 7547
% 0.20/0.54  % (25224)Time elapsed: 0.111 s
% 0.20/0.54  % (25224)------------------------------
% 0.20/0.54  % (25224)------------------------------
% 0.20/0.54  % (25217)Success in time 0.186 s
%------------------------------------------------------------------------------
