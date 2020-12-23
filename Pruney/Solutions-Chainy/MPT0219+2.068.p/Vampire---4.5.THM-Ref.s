%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:30 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 324 expanded)
%              Number of leaves         :   21 ( 107 expanded)
%              Depth                    :   22
%              Number of atoms          :  271 ( 628 expanded)
%              Number of equality atoms :  104 ( 370 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1486,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1482,f43])).

fof(f43,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK4 != sK5
    & k1_tarski(sK4) = k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK4 != sK5
      & k1_tarski(sK4) = k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f1482,plain,(
    sK4 = sK5 ),
    inference(resolution,[],[f1481,f84])).

fof(f84,plain,(
    ! [X2,X3,X1] : sP2(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X1,X0] :
      ( sP2(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1481,plain,(
    ! [X0] :
      ( ~ sP2(X0,sK5,sK5,sK5)
      | sK4 = X0 ) ),
    inference(duplicate_literal_removal,[],[f1479])).

fof(f1479,plain,(
    ! [X0] :
      ( ~ sP2(X0,sK5,sK5,sK5)
      | sK4 = X0
      | sK4 = X0
      | sK4 = X0 ) ),
    inference(resolution,[],[f1475,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | X0 = X2
      | X0 = X3
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1475,plain,(
    ! [X0] :
      ( sP2(X0,sK4,sK4,sK4)
      | ~ sP2(X0,sK5,sK5,sK5) ) ),
    inference(resolution,[],[f255,f1459])).

fof(f1459,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
      | sP2(X0,sK4,sK4,sK4) ) ),
    inference(resolution,[],[f1457,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] : sP3(X0,X1,X2,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP3(X0,X1,X2,X3) )
      & ( sP3(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP3(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f17,f22,f21])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( sP3(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP2(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1457,plain,(
    ! [X0,X1] :
      ( ~ sP3(sK5,sK5,sK5,X1)
      | sP2(X0,sK4,sK4,sK4)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f214,f1175])).

fof(f1175,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
      | ~ sP3(sK5,sK5,sK5,X3)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f809,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f809,plain,(
    ! [X10,X11] :
      ( sP0(X10,X11,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
      | ~ r2_hidden(X11,X10)
      | ~ sP3(sK5,sK5,sK5,X10) ) ),
    inference(superposition,[],[f123,f778])).

fof(f778,plain,(
    ! [X4] :
      ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X4) = X4
      | ~ sP3(sK5,sK5,sK5,X4) ) ),
    inference(forward_demodulation,[],[f723,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f723,plain,(
    ! [X4] :
      ( k5_xboole_0(X4,k1_xboole_0) = k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X4)
      | ~ sP3(sK5,sK5,sK5,X4) ) ),
    inference(superposition,[],[f429,f691])).

fof(f691,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0))
      | ~ sP3(sK5,sK5,sK5,X0) ) ),
    inference(superposition,[],[f551,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_enumset1(X0,X0,X0,X1,X2) = X3
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f73,f75])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f551,plain,(
    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5))) ),
    inference(forward_demodulation,[],[f549,f320])).

fof(f320,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f79,f80])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f48,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f47,f50,f74])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f549,plain,(
    k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[],[f429,f490])).

fof(f490,plain,(
    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5)))) ),
    inference(forward_demodulation,[],[f78,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f78,plain,(
    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f42,f77,f74,f77,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f75])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    k1_tarski(sK4) = k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f25])).

fof(f429,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f323,f416])).

fof(f416,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,X8) = X8 ),
    inference(forward_demodulation,[],[f392,f44])).

fof(f392,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,k1_xboole_0) ),
    inference(superposition,[],[f323,f320])).

fof(f323,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f53,f320])).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f54,f83])).

fof(f83,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f19,f18])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f214,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
      | sP2(X0,X3,X2,X1) ) ),
    inference(resolution,[],[f64,f87])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | ~ r2_hidden(X5,X3)
      | sP2(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( ( ~ sP2(sK7(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sP2(sK7(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X5,X2,X1,X0) )
            & ( sP2(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP2(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP2(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP2(sK7(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sP2(sK7(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X5,X2,X1,X0) )
            & ( sP2(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP2(X4,X2,X1,X0) )
            & ( sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f255,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k3_enumset1(X3,X3,X3,X2,X1))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f65,f87])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | ~ sP2(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (18567)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.48  % (18575)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.49  % (18571)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.50  % (18575)Refutation not found, incomplete strategy% (18575)------------------------------
% 0.19/0.50  % (18575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (18575)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (18575)Memory used [KB]: 10618
% 0.19/0.50  % (18575)Time elapsed: 0.091 s
% 0.19/0.50  % (18575)------------------------------
% 0.19/0.50  % (18575)------------------------------
% 0.19/0.50  % (18570)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.50  % (18584)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.50  % (18576)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (18588)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.50  % (18576)Refutation not found, incomplete strategy% (18576)------------------------------
% 0.19/0.50  % (18576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (18576)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (18576)Memory used [KB]: 10618
% 0.19/0.50  % (18576)Time elapsed: 0.105 s
% 0.19/0.50  % (18576)------------------------------
% 0.19/0.50  % (18576)------------------------------
% 0.19/0.50  % (18582)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.51  % (18569)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (18582)Refutation not found, incomplete strategy% (18582)------------------------------
% 0.19/0.51  % (18582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (18582)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (18582)Memory used [KB]: 10618
% 0.19/0.51  % (18582)Time elapsed: 0.107 s
% 0.19/0.51  % (18582)------------------------------
% 0.19/0.51  % (18582)------------------------------
% 0.19/0.51  % (18568)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (18565)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (18587)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (18572)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (18580)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (18579)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (18592)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.52  % (18573)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.52  % (18589)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (18586)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.52  % (18566)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.53  % (18581)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (18578)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.53  % (18565)Refutation not found, incomplete strategy% (18565)------------------------------
% 0.19/0.53  % (18565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (18565)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (18565)Memory used [KB]: 1663
% 0.19/0.53  % (18565)Time elapsed: 0.111 s
% 0.19/0.53  % (18565)------------------------------
% 0.19/0.53  % (18565)------------------------------
% 0.19/0.53  % (18590)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (18577)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % (18593)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (18591)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.54  % (18583)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.54  % (18574)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (18574)Refutation not found, incomplete strategy% (18574)------------------------------
% 1.41/0.55  % (18574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (18574)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (18574)Memory used [KB]: 10618
% 1.41/0.55  % (18574)Time elapsed: 0.139 s
% 1.41/0.55  % (18574)------------------------------
% 1.41/0.55  % (18574)------------------------------
% 1.41/0.55  % (18585)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (18594)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.54/0.61  % (18681)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.54/0.62  % (18675)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.05/0.63  % (18592)Refutation found. Thanks to Tanya!
% 2.05/0.63  % SZS status Theorem for theBenchmark
% 2.05/0.63  % SZS output start Proof for theBenchmark
% 2.05/0.63  fof(f1486,plain,(
% 2.05/0.63    $false),
% 2.05/0.63    inference(subsumption_resolution,[],[f1482,f43])).
% 2.05/0.63  fof(f43,plain,(
% 2.05/0.63    sK4 != sK5),
% 2.05/0.63    inference(cnf_transformation,[],[f25])).
% 2.05/0.63  fof(f25,plain,(
% 2.05/0.63    sK4 != sK5 & k1_tarski(sK4) = k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f24])).
% 2.05/0.63  fof(f24,plain,(
% 2.05/0.63    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK4 != sK5 & k1_tarski(sK4) = k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f16,plain,(
% 2.05/0.63    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.05/0.63    inference(ennf_transformation,[],[f15])).
% 2.05/0.63  fof(f15,negated_conjecture,(
% 2.05/0.63    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.05/0.63    inference(negated_conjecture,[],[f14])).
% 2.05/0.63  fof(f14,conjecture,(
% 2.05/0.63    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 2.05/0.63  fof(f1482,plain,(
% 2.05/0.63    sK4 = sK5),
% 2.05/0.63    inference(resolution,[],[f1481,f84])).
% 2.05/0.63  fof(f84,plain,(
% 2.05/0.63    ( ! [X2,X3,X1] : (sP2(X1,X1,X2,X3)) )),
% 2.05/0.63    inference(equality_resolution,[],[f71])).
% 2.05/0.63  fof(f71,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | X0 != X1) )),
% 2.05/0.63    inference(cnf_transformation,[],[f40])).
% 2.05/0.63  fof(f40,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP2(X0,X1,X2,X3)))),
% 2.05/0.63    inference(rectify,[],[f39])).
% 2.05/0.63  fof(f39,plain,(
% 2.05/0.63    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP2(X4,X2,X1,X0)))),
% 2.05/0.63    inference(flattening,[],[f38])).
% 2.05/0.63  fof(f38,plain,(
% 2.05/0.63    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP2(X4,X2,X1,X0)))),
% 2.05/0.63    inference(nnf_transformation,[],[f21])).
% 2.05/0.63  fof(f21,plain,(
% 2.05/0.63    ! [X4,X2,X1,X0] : (sP2(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 2.05/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.05/0.63  fof(f1481,plain,(
% 2.05/0.63    ( ! [X0] : (~sP2(X0,sK5,sK5,sK5) | sK4 = X0) )),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f1479])).
% 2.05/0.63  fof(f1479,plain,(
% 2.05/0.63    ( ! [X0] : (~sP2(X0,sK5,sK5,sK5) | sK4 = X0 | sK4 = X0 | sK4 = X0) )),
% 2.05/0.63    inference(resolution,[],[f1475,f68])).
% 2.05/0.63  fof(f68,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3) | X0 = X2 | X0 = X3 | X0 = X1) )),
% 2.05/0.63    inference(cnf_transformation,[],[f40])).
% 2.05/0.63  fof(f1475,plain,(
% 2.05/0.63    ( ! [X0] : (sP2(X0,sK4,sK4,sK4) | ~sP2(X0,sK5,sK5,sK5)) )),
% 2.05/0.63    inference(resolution,[],[f255,f1459])).
% 2.05/0.63  fof(f1459,plain,(
% 2.05/0.63    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) | sP2(X0,sK4,sK4,sK4)) )),
% 2.05/0.63    inference(resolution,[],[f1457,f87])).
% 2.05/0.63  fof(f87,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (sP3(X0,X1,X2,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 2.05/0.63    inference(equality_resolution,[],[f82])).
% 2.05/0.63  fof(f82,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.05/0.63    inference(definition_unfolding,[],[f72,f75])).
% 2.05/0.63  fof(f75,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f52,f63])).
% 2.05/0.63  fof(f63,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f13])).
% 2.05/0.63  fof(f13,axiom,(
% 2.05/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.05/0.63  fof(f52,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f12])).
% 2.05/0.63  fof(f12,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.05/0.63  fof(f72,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f41,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) & (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 2.05/0.63    inference(nnf_transformation,[],[f23])).
% 2.05/0.63  fof(f23,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP3(X0,X1,X2,X3))),
% 2.05/0.63    inference(definition_folding,[],[f17,f22,f21])).
% 2.05/0.63  fof(f22,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : (sP3(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP2(X4,X2,X1,X0)))),
% 2.05/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.05/0.63  fof(f17,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.05/0.63    inference(ennf_transformation,[],[f9])).
% 2.05/0.63  fof(f9,axiom,(
% 2.05/0.63    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.05/0.63  fof(f1457,plain,(
% 2.05/0.63    ( ! [X0,X1] : (~sP3(sK5,sK5,sK5,X1) | sP2(X0,sK4,sK4,sK4) | ~r2_hidden(X0,X1)) )),
% 2.05/0.63    inference(resolution,[],[f214,f1175])).
% 2.05/0.63  fof(f1175,plain,(
% 2.05/0.63    ( ! [X2,X3] : (r2_hidden(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~sP3(sK5,sK5,sK5,X3) | ~r2_hidden(X2,X3)) )),
% 2.05/0.63    inference(resolution,[],[f809,f58])).
% 2.05/0.63  fof(f58,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f32])).
% 2.05/0.63  fof(f32,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 2.05/0.63    inference(rectify,[],[f31])).
% 2.05/0.63  fof(f31,plain,(
% 2.05/0.63    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 2.05/0.63    inference(flattening,[],[f30])).
% 2.05/0.63  fof(f30,plain,(
% 2.05/0.63    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 2.05/0.63    inference(nnf_transformation,[],[f18])).
% 2.05/0.63  fof(f18,plain,(
% 2.05/0.63    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 2.05/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.05/0.63  fof(f809,plain,(
% 2.05/0.63    ( ! [X10,X11] : (sP0(X10,X11,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~r2_hidden(X11,X10) | ~sP3(sK5,sK5,sK5,X10)) )),
% 2.05/0.63    inference(superposition,[],[f123,f778])).
% 2.05/0.63  fof(f778,plain,(
% 2.05/0.63    ( ! [X4] : (k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X4) = X4 | ~sP3(sK5,sK5,sK5,X4)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f723,f44])).
% 2.05/0.63  fof(f44,plain,(
% 2.05/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.05/0.63    inference(cnf_transformation,[],[f6])).
% 2.05/0.63  fof(f6,axiom,(
% 2.05/0.63    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.05/0.63  fof(f723,plain,(
% 2.05/0.63    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X4) | ~sP3(sK5,sK5,sK5,X4)) )),
% 2.05/0.63    inference(superposition,[],[f429,f691])).
% 2.05/0.63  fof(f691,plain,(
% 2.05/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) | ~sP3(sK5,sK5,sK5,X0)) )),
% 2.05/0.63    inference(superposition,[],[f551,f81])).
% 2.05/0.63  fof(f81,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f73,f75])).
% 2.05/0.63  fof(f73,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f551,plain,(
% 2.05/0.63    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5)))),
% 2.05/0.63    inference(forward_demodulation,[],[f549,f320])).
% 2.05/0.63  fof(f320,plain,(
% 2.05/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f79,f80])).
% 2.05/0.63  fof(f80,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 2.05/0.63    inference(definition_unfolding,[],[f48,f74])).
% 2.05/0.63  fof(f74,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f51,f50])).
% 2.05/0.63  fof(f50,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f3])).
% 2.05/0.63  fof(f3,axiom,(
% 2.05/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.05/0.63  fof(f51,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f8])).
% 2.05/0.63  fof(f8,axiom,(
% 2.05/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.05/0.63  fof(f48,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.05/0.63    inference(cnf_transformation,[],[f4])).
% 2.05/0.63  fof(f4,axiom,(
% 2.05/0.63    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.05/0.63  fof(f79,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f47,f50,f74])).
% 2.05/0.63  fof(f47,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.05/0.63    inference(cnf_transformation,[],[f5])).
% 2.05/0.63  fof(f5,axiom,(
% 2.05/0.63    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.05/0.63  fof(f549,plain,(
% 2.05/0.63    k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 2.05/0.63    inference(superposition,[],[f429,f490])).
% 2.05/0.63  fof(f490,plain,(
% 2.05/0.63    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5))))),
% 2.05/0.63    inference(forward_demodulation,[],[f78,f46])).
% 2.05/0.63  fof(f46,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f1])).
% 2.05/0.63  fof(f1,axiom,(
% 2.05/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.05/0.63  fof(f78,plain,(
% 2.05/0.63    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4))))),
% 2.05/0.63    inference(definition_unfolding,[],[f42,f77,f74,f77,f77])).
% 2.05/0.63  fof(f77,plain,(
% 2.05/0.63    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f45,f76])).
% 2.05/0.63  fof(f76,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f49,f75])).
% 2.05/0.63  fof(f49,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f11])).
% 2.05/0.63  fof(f11,axiom,(
% 2.05/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.05/0.63  fof(f45,plain,(
% 2.05/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f10])).
% 2.05/0.63  fof(f10,axiom,(
% 2.05/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.05/0.63  fof(f42,plain,(
% 2.05/0.63    k1_tarski(sK4) = k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),
% 2.05/0.63    inference(cnf_transformation,[],[f25])).
% 2.05/0.63  fof(f429,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.05/0.63    inference(backward_demodulation,[],[f323,f416])).
% 2.05/0.63  fof(f416,plain,(
% 2.05/0.63    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = X8) )),
% 2.05/0.63    inference(forward_demodulation,[],[f392,f44])).
% 2.05/0.63  fof(f392,plain,(
% 2.05/0.63    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,k1_xboole_0)) )),
% 2.05/0.63    inference(superposition,[],[f323,f320])).
% 2.05/0.63  fof(f323,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(superposition,[],[f53,f320])).
% 2.05/0.63  fof(f53,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f7])).
% 2.05/0.63  fof(f7,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.05/0.63  fof(f123,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 2.05/0.63    inference(resolution,[],[f54,f83])).
% 2.05/0.63  fof(f83,plain,(
% 2.05/0.63    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(equality_resolution,[],[f61])).
% 2.05/0.63  fof(f61,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.05/0.63    inference(cnf_transformation,[],[f33])).
% 2.05/0.63  fof(f33,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 2.05/0.63    inference(nnf_transformation,[],[f20])).
% 2.05/0.63  fof(f20,plain,(
% 2.05/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 2.05/0.63    inference(definition_folding,[],[f2,f19,f18])).
% 2.05/0.63  fof(f19,plain,(
% 2.05/0.63    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 2.05/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.05/0.63  fof(f2,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.05/0.63  fof(f54,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f29])).
% 2.05/0.63  fof(f29,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).
% 2.05/0.63  fof(f28,plain,(
% 2.05/0.63    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f27,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.05/0.63    inference(rectify,[],[f26])).
% 2.05/0.63  fof(f26,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 2.05/0.63    inference(nnf_transformation,[],[f19])).
% 2.05/0.63  fof(f214,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) | sP2(X0,X3,X2,X1)) )),
% 2.05/0.63    inference(resolution,[],[f64,f87])).
% 2.05/0.63  fof(f64,plain,(
% 2.05/0.63    ( ! [X2,X0,X5,X3,X1] : (~sP3(X0,X1,X2,X3) | ~r2_hidden(X5,X3) | sP2(X5,X2,X1,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f37])).
% 2.05/0.63  fof(f37,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ((~sP2(sK7(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sP2(sK7(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).
% 2.05/0.63  fof(f36,plain,(
% 2.05/0.63    ! [X3,X2,X1,X0] : (? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP2(sK7(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sP2(sK7(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f35,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 2.05/0.63    inference(rectify,[],[f34])).
% 2.05/0.63  fof(f34,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP2(X4,X2,X1,X0)) & (sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP3(X0,X1,X2,X3)))),
% 2.05/0.63    inference(nnf_transformation,[],[f22])).
% 2.05/0.63  fof(f255,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k3_enumset1(X3,X3,X3,X2,X1)) | ~sP2(X0,X1,X2,X3)) )),
% 2.05/0.63    inference(resolution,[],[f65,f87])).
% 2.05/0.63  fof(f65,plain,(
% 2.05/0.63    ( ! [X2,X0,X5,X3,X1] : (~sP3(X0,X1,X2,X3) | ~sP2(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f37])).
% 2.05/0.63  % SZS output end Proof for theBenchmark
% 2.05/0.63  % (18592)------------------------------
% 2.05/0.63  % (18592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (18592)Termination reason: Refutation
% 2.05/0.63  
% 2.05/0.63  % (18592)Memory used [KB]: 7036
% 2.05/0.63  % (18592)Time elapsed: 0.231 s
% 2.05/0.63  % (18592)------------------------------
% 2.05/0.63  % (18592)------------------------------
% 2.05/0.63  % (18562)Success in time 0.269 s
%------------------------------------------------------------------------------
