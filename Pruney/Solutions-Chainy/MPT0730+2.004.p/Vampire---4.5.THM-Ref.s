%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:13 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  123 (1755 expanded)
%              Number of leaves         :   23 ( 515 expanded)
%              Depth                    :   26
%              Number of atoms          :  324 (3421 expanded)
%              Number of equality atoms :   83 (1533 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f550,plain,(
    $false ),
    inference(subsumption_resolution,[],[f549,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X0)))) ),
    inference(resolution,[],[f111,f110])).

fof(f110,plain,(
    ! [X0,X1] : r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) ),
    inference(resolution,[],[f93,f98])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f70,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f111,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(k5_enumset1(X4,X4,X4,X4,X4,X4,X2),X3)
      | r2_hidden(X2,k3_tarski(X3)) ) ),
    inference(resolution,[],[f93,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f549,plain,(
    ~ r2_hidden(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f548,f510])).

fof(f510,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f509,f379])).

fof(f379,plain,
    ( r2_hidden(sK1,sK2)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f376,f273])).

fof(f273,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f272,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f272,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1)
    | r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1)
    | sK1 = sK2
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f144,f186])).

fof(f186,plain,
    ( r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK1 = sK2
    | r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f185,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X0) ) ),
    inference(resolution,[],[f113,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f71,f83])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f113,plain,(
    ! [X4,X3] : ~ r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4),X4) ),
    inference(resolution,[],[f110,f66])).

fof(f185,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK2,sK2) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK2,sK2)
    | r2_hidden(sK2,sK2) ),
    inference(resolution,[],[f141,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | r2_hidden(X2,X0)
      | r2_hidden(X1,X0) ) ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( X0 != X0
      | r1_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | r2_hidden(X2,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f62,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f72,f83])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f141,plain,
    ( ~ r1_xboole_0(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK1 = sK2
    | r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f136,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X0)
        & r2_hidden(X1,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f136,plain,
    ( r2_hidden(sK1,sK2)
    | sK1 = sK2
    | sP0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1,sK2)
    | r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r1_xboole_0(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f89,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
      | sP0(X1,X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f83])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | sP0(X1,X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | sP0(X1,X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_folding,[],[f32,f33])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f89,plain,
    ( r2_hidden(sK1,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | r2_hidden(sK1,sK2)
    | sK1 = sK2 ),
    inference(definition_unfolding,[],[f49,f86])).

fof(f86,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f54,f84,f85])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f49,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ( sK1 != sK2
        & ~ r2_hidden(sK1,sK2) )
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( sK1 = sK2
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_ordinal1(X1)) )
        & ( X0 = X1
          | r2_hidden(X0,X1)
          | r2_hidden(X0,k1_ordinal1(X1)) ) )
   => ( ( ( sK1 != sK2
          & ~ r2_hidden(sK1,sK2) )
        | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
      & ( sK1 = sK2
        | r2_hidden(sK1,sK2)
        | r2_hidden(sK1,k1_ordinal1(sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <~> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,k1_ordinal1(X1))
      <=> ( X0 = X1
          | r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f104,f91])).

fof(f91,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f84])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_tarski(X1),X2)
      | k3_tarski(X1) = X2
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f61,f58])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f376,plain,
    ( r2_hidden(sK1,sK2)
    | sK1 = sK2
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f257,f98])).

fof(f257,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r2_hidden(sK1,sK2)
      | sK1 = sK2
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f186,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
      | ~ r1_tarski(X2,X1)
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f68,f90])).

fof(f90,plain,(
    ! [X0] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f85])).

fof(f52,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f509,plain,
    ( sK1 = sK2
    | ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f500,f114])).

fof(f114,plain,(
    ! [X0,X1] : r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f94,f98])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f500,plain,
    ( sK1 = sK2
    | ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f490,f88])).

fof(f88,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f50,f86])).

fof(f50,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f490,plain,(
    ! [X2] :
      ( r2_hidden(sK1,k3_tarski(X2))
      | sK1 = sK2
      | ~ r2_hidden(sK2,X2) ) ),
    inference(resolution,[],[f401,f58])).

fof(f401,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | r2_hidden(sK1,X0)
      | sK1 = sK2 ) ),
    inference(resolution,[],[f379,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f548,plain,(
    ~ r2_hidden(sK1,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(trivial_inequality_removal,[],[f546])).

fof(f546,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK1,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(backward_demodulation,[],[f87,f510])).

fof(f87,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f51,f86])).

fof(f51,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:35:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (25837)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.50  % (25829)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (25821)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (25818)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (25820)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (25819)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (25815)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (25827)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (25835)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (25836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (25835)Refutation not found, incomplete strategy% (25835)------------------------------
% 0.22/0.53  % (25835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25835)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25835)Memory used [KB]: 1663
% 0.22/0.53  % (25835)Time elapsed: 0.130 s
% 0.22/0.53  % (25835)------------------------------
% 0.22/0.53  % (25835)------------------------------
% 0.22/0.53  % (25838)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (25814)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (25814)Refutation not found, incomplete strategy% (25814)------------------------------
% 0.22/0.54  % (25814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25814)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25814)Memory used [KB]: 1663
% 0.22/0.54  % (25814)Time elapsed: 0.127 s
% 0.22/0.54  % (25814)------------------------------
% 0.22/0.54  % (25814)------------------------------
% 0.22/0.54  % (25842)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (25843)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (25816)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (25828)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (25817)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (25830)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (25841)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (25839)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (25833)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (25834)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (25822)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (25825)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (25831)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (25831)Refutation not found, incomplete strategy% (25831)------------------------------
% 0.22/0.55  % (25831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (25825)Refutation not found, incomplete strategy% (25825)------------------------------
% 0.22/0.55  % (25825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (25831)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  % (25825)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  
% 0.22/0.55  % (25831)Memory used [KB]: 10618
% 0.22/0.55  % (25825)Memory used [KB]: 10618
% 0.22/0.55  % (25831)Time elapsed: 0.149 s
% 0.22/0.55  % (25825)Time elapsed: 0.149 s
% 0.22/0.55  % (25831)------------------------------
% 0.22/0.55  % (25831)------------------------------
% 0.22/0.55  % (25825)------------------------------
% 0.22/0.55  % (25825)------------------------------
% 0.22/0.55  % (25826)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (25823)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (25823)Refutation not found, incomplete strategy% (25823)------------------------------
% 0.22/0.56  % (25823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (25823)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (25823)Memory used [KB]: 10618
% 0.22/0.56  % (25823)Time elapsed: 0.151 s
% 0.22/0.56  % (25823)------------------------------
% 0.22/0.56  % (25823)------------------------------
% 0.22/0.58  % (25824)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.59  % (25840)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.59  % (25832)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.81/0.61  % (25824)Refutation not found, incomplete strategy% (25824)------------------------------
% 1.81/0.61  % (25824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (25824)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (25824)Memory used [KB]: 10618
% 1.81/0.61  % (25824)Time elapsed: 0.171 s
% 1.81/0.61  % (25824)------------------------------
% 1.81/0.61  % (25824)------------------------------
% 1.81/0.62  % (25843)Refutation found. Thanks to Tanya!
% 1.81/0.62  % SZS status Theorem for theBenchmark
% 1.81/0.62  % SZS output start Proof for theBenchmark
% 1.81/0.62  fof(f550,plain,(
% 1.81/0.62    $false),
% 1.81/0.62    inference(subsumption_resolution,[],[f549,f167])).
% 1.81/0.62  fof(f167,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X0))))) )),
% 1.81/0.62    inference(resolution,[],[f111,f110])).
% 1.81/0.62  fof(f110,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) )),
% 1.81/0.62    inference(resolution,[],[f93,f98])).
% 1.81/0.62  fof(f98,plain,(
% 1.81/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.81/0.62    inference(equality_resolution,[],[f60])).
% 1.81/0.62  fof(f60,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.81/0.62    inference(cnf_transformation,[],[f40])).
% 1.81/0.62  fof(f40,plain,(
% 1.81/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.62    inference(flattening,[],[f39])).
% 1.81/0.62  fof(f39,plain,(
% 1.81/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.62    inference(nnf_transformation,[],[f4])).
% 1.81/0.62  fof(f4,axiom,(
% 1.81/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.81/0.62  fof(f93,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.81/0.62    inference(definition_unfolding,[],[f70,f83])).
% 1.81/0.62  fof(f83,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.81/0.62    inference(definition_unfolding,[],[f57,f82])).
% 1.81/0.62  fof(f82,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.81/0.62    inference(definition_unfolding,[],[f67,f81])).
% 1.81/0.62  fof(f81,plain,(
% 1.81/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.81/0.62    inference(definition_unfolding,[],[f77,f80])).
% 1.81/0.62  fof(f80,plain,(
% 1.81/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.81/0.62    inference(definition_unfolding,[],[f78,f79])).
% 1.81/0.62  fof(f79,plain,(
% 1.81/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f11])).
% 1.81/0.62  fof(f11,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.81/0.62  fof(f78,plain,(
% 1.81/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f10])).
% 1.81/0.62  fof(f10,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.81/0.62  fof(f77,plain,(
% 1.81/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f9])).
% 1.81/0.62  fof(f9,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.81/0.62  fof(f67,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f8])).
% 1.81/0.62  fof(f8,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.81/0.62  fof(f57,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f7])).
% 1.81/0.62  fof(f7,axiom,(
% 1.81/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.81/0.62  fof(f70,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f46])).
% 1.81/0.62  fof(f46,plain,(
% 1.81/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.81/0.62    inference(flattening,[],[f45])).
% 1.81/0.62  fof(f45,plain,(
% 1.81/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.81/0.62    inference(nnf_transformation,[],[f15])).
% 1.81/0.62  fof(f15,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.81/0.62  fof(f111,plain,(
% 1.81/0.62    ( ! [X4,X2,X3] : (~r2_hidden(k5_enumset1(X4,X4,X4,X4,X4,X4,X2),X3) | r2_hidden(X2,k3_tarski(X3))) )),
% 1.81/0.62    inference(resolution,[],[f93,f58])).
% 1.81/0.62  fof(f58,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f25])).
% 1.81/0.62  fof(f25,plain,(
% 1.81/0.62    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.81/0.62    inference(ennf_transformation,[],[f12])).
% 1.81/0.62  fof(f12,axiom,(
% 1.81/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.81/0.62  fof(f549,plain,(
% 1.81/0.62    ~r2_hidden(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.81/0.62    inference(forward_demodulation,[],[f548,f510])).
% 1.81/0.62  fof(f510,plain,(
% 1.81/0.62    sK1 = sK2),
% 1.81/0.62    inference(subsumption_resolution,[],[f509,f379])).
% 1.81/0.62  fof(f379,plain,(
% 1.81/0.62    r2_hidden(sK1,sK2) | sK1 = sK2),
% 1.81/0.62    inference(subsumption_resolution,[],[f376,f273])).
% 1.81/0.62  fof(f273,plain,(
% 1.81/0.62    ~r1_tarski(sK2,sK1) | sK1 = sK2),
% 1.81/0.62    inference(subsumption_resolution,[],[f272,f66])).
% 1.81/0.62  fof(f66,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f28])).
% 1.81/0.62  fof(f28,plain,(
% 1.81/0.62    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.81/0.62    inference(ennf_transformation,[],[f19])).
% 1.81/0.62  fof(f19,axiom,(
% 1.81/0.62    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.81/0.62  fof(f272,plain,(
% 1.81/0.62    sK1 = sK2 | ~r1_tarski(sK2,sK1) | r2_hidden(sK1,sK2)),
% 1.81/0.62    inference(duplicate_literal_removal,[],[f271])).
% 1.81/0.62  fof(f271,plain,(
% 1.81/0.62    sK1 = sK2 | ~r1_tarski(sK2,sK1) | sK1 = sK2 | r2_hidden(sK1,sK2)),
% 1.81/0.62    inference(resolution,[],[f144,f186])).
% 1.81/0.62  fof(f186,plain,(
% 1.81/0.62    r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | sK1 = sK2 | r2_hidden(sK1,sK2)),
% 1.81/0.62    inference(subsumption_resolution,[],[f185,f124])).
% 1.81/0.62  fof(f124,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X0)) )),
% 1.81/0.62    inference(resolution,[],[f113,f92])).
% 1.81/0.62  fof(f92,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.81/0.62    inference(definition_unfolding,[],[f71,f83])).
% 1.81/0.62  fof(f71,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f46])).
% 1.81/0.62  fof(f113,plain,(
% 1.81/0.62    ( ! [X4,X3] : (~r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4),X4)) )),
% 1.81/0.62    inference(resolution,[],[f110,f66])).
% 1.81/0.62  fof(f185,plain,(
% 1.81/0.62    sK1 = sK2 | r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(sK1,sK2) | r2_hidden(sK2,sK2)),
% 1.81/0.62    inference(duplicate_literal_removal,[],[f184])).
% 1.81/0.62  fof(f184,plain,(
% 1.81/0.62    sK1 = sK2 | r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(sK1,sK2) | r2_hidden(sK2,sK2) | r2_hidden(sK2,sK2)),
% 1.81/0.62    inference(resolution,[],[f141,f123])).
% 1.81/0.62  fof(f123,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | r2_hidden(X2,X0) | r2_hidden(X1,X0)) )),
% 1.81/0.62    inference(trivial_inequality_removal,[],[f122])).
% 1.81/0.62  fof(f122,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (X0 != X0 | r1_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | r2_hidden(X2,X0) | r2_hidden(X1,X0)) )),
% 1.81/0.62    inference(superposition,[],[f62,f95])).
% 1.81/0.62  fof(f95,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.81/0.62    inference(definition_unfolding,[],[f72,f83])).
% 1.81/0.62  fof(f72,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f31])).
% 1.81/0.62  fof(f31,plain,(
% 1.81/0.62    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 1.81/0.62    inference(ennf_transformation,[],[f14])).
% 1.81/0.62  fof(f14,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.81/0.62  fof(f62,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f26])).
% 1.81/0.62  fof(f26,plain,(
% 1.81/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 1.81/0.62    inference(ennf_transformation,[],[f23])).
% 1.81/0.62  fof(f23,plain,(
% 1.81/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 1.81/0.62    inference(unused_predicate_definition_removal,[],[f5])).
% 1.81/0.62  fof(f5,axiom,(
% 1.81/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.81/0.62  fof(f141,plain,(
% 1.81/0.62    ~r1_xboole_0(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | sK1 = sK2 | r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(sK1,sK2)),
% 1.81/0.62    inference(subsumption_resolution,[],[f136,f73])).
% 1.81/0.62  fof(f73,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f48])).
% 1.81/0.62  fof(f48,plain,(
% 1.81/0.62    ! [X0,X1,X2] : ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2))),
% 1.81/0.62    inference(rectify,[],[f47])).
% 1.81/0.62  fof(f47,plain,(
% 1.81/0.62    ! [X1,X2,X0] : ((~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~sP0(X1,X2,X0))),
% 1.81/0.62    inference(nnf_transformation,[],[f33])).
% 1.81/0.62  fof(f33,plain,(
% 1.81/0.62    ! [X1,X2,X0] : ((~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~sP0(X1,X2,X0))),
% 1.81/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.81/0.62  fof(f136,plain,(
% 1.81/0.62    r2_hidden(sK1,sK2) | sK1 = sK2 | sP0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1,sK2) | r2_hidden(sK1,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~r1_xboole_0(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.81/0.62    inference(resolution,[],[f89,f97])).
% 1.81/0.62  fof(f97,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) | sP0(X1,X2,X0) | r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.81/0.62    inference(definition_unfolding,[],[f75,f84])).
% 1.81/0.62  fof(f84,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.81/0.62    inference(definition_unfolding,[],[f56,f83])).
% 1.81/0.62  fof(f56,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f13])).
% 1.81/0.62  fof(f13,axiom,(
% 1.81/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.81/0.62  fof(f75,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | sP0(X1,X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f34])).
% 1.81/0.62  fof(f34,plain,(
% 1.81/0.62    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | sP0(X1,X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.81/0.62    inference(definition_folding,[],[f32,f33])).
% 1.81/0.62  fof(f32,plain,(
% 1.81/0.62    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.81/0.62    inference(ennf_transformation,[],[f3])).
% 1.81/0.62  fof(f3,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).
% 1.81/0.62  fof(f89,plain,(
% 1.81/0.62    r2_hidden(sK1,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | r2_hidden(sK1,sK2) | sK1 = sK2),
% 1.81/0.62    inference(definition_unfolding,[],[f49,f86])).
% 1.81/0.62  fof(f86,plain,(
% 1.81/0.62    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.81/0.62    inference(definition_unfolding,[],[f54,f84,f85])).
% 1.81/0.62  fof(f85,plain,(
% 1.81/0.62    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.81/0.62    inference(definition_unfolding,[],[f53,f83])).
% 1.81/0.62  fof(f53,plain,(
% 1.81/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f6])).
% 1.81/0.62  fof(f6,axiom,(
% 1.81/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.81/0.62  fof(f54,plain,(
% 1.81/0.62    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f18])).
% 1.81/0.62  fof(f18,axiom,(
% 1.81/0.62    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.81/0.62  fof(f49,plain,(
% 1.81/0.62    sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.81/0.62    inference(cnf_transformation,[],[f38])).
% 1.81/0.62  fof(f38,plain,(
% 1.81/0.62    ((sK1 != sK2 & ~r2_hidden(sK1,sK2)) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2)))),
% 1.81/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f37])).
% 1.81/0.62  fof(f37,plain,(
% 1.81/0.62    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) => (((sK1 != sK2 & ~r2_hidden(sK1,sK2)) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.62  fof(f36,plain,(
% 1.81/0.62    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))))),
% 1.81/0.62    inference(flattening,[],[f35])).
% 1.81/0.62  fof(f35,plain,(
% 1.81/0.62    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | r2_hidden(X0,k1_ordinal1(X1))))),
% 1.81/0.62    inference(nnf_transformation,[],[f24])).
% 1.81/0.62  fof(f24,plain,(
% 1.81/0.62    ? [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <~> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.81/0.62    inference(ennf_transformation,[],[f21])).
% 1.81/0.62  fof(f21,negated_conjecture,(
% 1.81/0.62    ~! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.81/0.62    inference(negated_conjecture,[],[f20])).
% 1.81/0.62  fof(f20,conjecture,(
% 1.81/0.62    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.81/0.62  fof(f144,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~r2_hidden(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/0.62    inference(superposition,[],[f104,f91])).
% 1.81/0.62  fof(f91,plain,(
% 1.81/0.62    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.81/0.62    inference(definition_unfolding,[],[f55,f84])).
% 1.81/0.62  fof(f55,plain,(
% 1.81/0.62    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.81/0.62    inference(cnf_transformation,[],[f22])).
% 1.81/0.62  fof(f22,plain,(
% 1.81/0.62    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.81/0.62    inference(rectify,[],[f2])).
% 1.81/0.62  fof(f2,axiom,(
% 1.81/0.62    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.81/0.62  fof(f104,plain,(
% 1.81/0.62    ( ! [X2,X1] : (~r1_tarski(k3_tarski(X1),X2) | k3_tarski(X1) = X2 | ~r2_hidden(X2,X1)) )),
% 1.81/0.62    inference(resolution,[],[f61,f58])).
% 1.81/0.62  fof(f61,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f40])).
% 1.81/0.62  fof(f376,plain,(
% 1.81/0.62    r2_hidden(sK1,sK2) | sK1 = sK2 | r1_tarski(sK2,sK1)),
% 1.81/0.62    inference(resolution,[],[f257,f98])).
% 1.81/0.62  fof(f257,plain,(
% 1.81/0.62    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK1,sK2) | sK1 = sK2 | r1_tarski(sK2,X0)) )),
% 1.81/0.62    inference(resolution,[],[f186,f108])).
% 1.81/0.62  fof(f108,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1)) )),
% 1.81/0.62    inference(superposition,[],[f68,f90])).
% 1.81/0.62  fof(f90,plain,(
% 1.81/0.62    ( ! [X0] : (k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.81/0.62    inference(definition_unfolding,[],[f52,f85])).
% 1.81/0.62  fof(f52,plain,(
% 1.81/0.62    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.81/0.62    inference(cnf_transformation,[],[f16])).
% 1.81/0.62  fof(f16,axiom,(
% 1.81/0.62    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.81/0.62  fof(f68,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f30])).
% 1.81/0.62  fof(f30,plain,(
% 1.81/0.62    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 1.81/0.62    inference(flattening,[],[f29])).
% 1.81/0.62  fof(f29,plain,(
% 1.81/0.62    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 1.81/0.62    inference(ennf_transformation,[],[f17])).
% 1.81/0.62  fof(f17,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).
% 1.81/0.62  fof(f509,plain,(
% 1.81/0.62    sK1 = sK2 | ~r2_hidden(sK1,sK2)),
% 1.81/0.62    inference(subsumption_resolution,[],[f500,f114])).
% 1.81/0.62  fof(f114,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.81/0.62    inference(resolution,[],[f94,f98])).
% 1.81/0.62  fof(f94,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.81/0.62    inference(definition_unfolding,[],[f69,f83])).
% 1.81/0.62  fof(f69,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f46])).
% 1.81/0.62  fof(f500,plain,(
% 1.81/0.62    sK1 = sK2 | ~r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | ~r2_hidden(sK1,sK2)),
% 1.81/0.62    inference(resolution,[],[f490,f88])).
% 1.81/0.62  fof(f88,plain,(
% 1.81/0.62    ~r2_hidden(sK1,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~r2_hidden(sK1,sK2)),
% 1.81/0.62    inference(definition_unfolding,[],[f50,f86])).
% 1.81/0.62  fof(f50,plain,(
% 1.81/0.62    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.81/0.62    inference(cnf_transformation,[],[f38])).
% 1.81/0.62  fof(f490,plain,(
% 1.81/0.62    ( ! [X2] : (r2_hidden(sK1,k3_tarski(X2)) | sK1 = sK2 | ~r2_hidden(sK2,X2)) )),
% 1.81/0.62    inference(resolution,[],[f401,f58])).
% 1.81/0.62  fof(f401,plain,(
% 1.81/0.62    ( ! [X0] : (~r1_tarski(sK2,X0) | r2_hidden(sK1,X0) | sK1 = sK2) )),
% 1.81/0.62    inference(resolution,[],[f379,f63])).
% 1.81/0.62  fof(f63,plain,(
% 1.81/0.62    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f44])).
% 1.81/0.62  fof(f44,plain,(
% 1.81/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.81/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 1.81/0.62  fof(f43,plain,(
% 1.81/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.62  fof(f42,plain,(
% 1.81/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.81/0.62    inference(rectify,[],[f41])).
% 1.81/0.62  fof(f41,plain,(
% 1.81/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.81/0.62    inference(nnf_transformation,[],[f27])).
% 1.81/0.62  fof(f27,plain,(
% 1.81/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.81/0.62    inference(ennf_transformation,[],[f1])).
% 1.81/0.62  fof(f1,axiom,(
% 1.81/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.81/0.62  fof(f548,plain,(
% 1.81/0.62    ~r2_hidden(sK1,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.81/0.62    inference(trivial_inequality_removal,[],[f546])).
% 1.81/0.62  fof(f546,plain,(
% 1.81/0.62    sK1 != sK1 | ~r2_hidden(sK1,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.81/0.62    inference(backward_demodulation,[],[f87,f510])).
% 1.81/0.62  fof(f87,plain,(
% 1.81/0.62    sK1 != sK2 | ~r2_hidden(sK1,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.81/0.62    inference(definition_unfolding,[],[f51,f86])).
% 1.81/0.62  fof(f51,plain,(
% 1.81/0.62    sK1 != sK2 | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.81/0.62    inference(cnf_transformation,[],[f38])).
% 1.81/0.62  % SZS output end Proof for theBenchmark
% 1.81/0.62  % (25843)------------------------------
% 1.81/0.62  % (25843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (25843)Termination reason: Refutation
% 1.81/0.62  
% 1.81/0.62  % (25843)Memory used [KB]: 2174
% 1.81/0.62  % (25843)Time elapsed: 0.211 s
% 1.81/0.62  % (25843)------------------------------
% 1.81/0.62  % (25843)------------------------------
% 1.97/0.62  % (25813)Success in time 0.254 s
%------------------------------------------------------------------------------
