%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:11 EST 2020

% Result     : Theorem 3.22s
% Output     : Refutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 618 expanded)
%              Number of leaves         :   32 ( 205 expanded)
%              Depth                    :   19
%              Number of atoms          :  411 (1186 expanded)
%              Number of equality atoms :   83 ( 484 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4771,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1564,f1642,f2642,f4769])).

fof(f4769,plain,
    ( ~ spl12_6
    | ~ spl12_12 ),
    inference(avatar_contradiction_clause,[],[f4768])).

fof(f4768,plain,
    ( $false
    | ~ spl12_6
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f4767,f1623])).

fof(f1623,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f1621])).

fof(f1621,plain,
    ( spl12_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f4767,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_6 ),
    inference(trivial_inequality_removal,[],[f4761])).

fof(f4761,plain,
    ( sK5 != sK5
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_6 ),
    inference(superposition,[],[f4756,f123])).

fof(f123,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f72,f120])).

fof(f120,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f76,f119])).

fof(f119,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f77,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f90,f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f113,f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f113,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f4756,plain,
    ( ! [X23] :
        ( sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,sK5,sK5,X23))
        | ~ v1_xboole_0(X23) )
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f4752,f1553])).

fof(f1553,plain,
    ( r1_tarski(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f1552])).

fof(f1552,plain,
    ( spl12_6
  <=> r1_tarski(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f4752,plain,(
    ! [X23] :
      ( ~ r1_tarski(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5)
      | ~ v1_xboole_0(X23)
      | sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,sK5,sK5,X23)) ) ),
    inference(resolution,[],[f4112,f1533])).

fof(f1533,plain,(
    ! [X24] :
      ( ~ sP1(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5,X24)
      | sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,sK5,sK5,X24)) ) ),
    inference(superposition,[],[f1204,f489])).

fof(f489,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0)) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(superposition,[],[f124,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f100,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f32,f31])).

fof(f31,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f124,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f79,f120,f78,f120])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1204,plain,(
    sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,sK5,sK5,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6))) ),
    inference(forward_demodulation,[],[f1151,f685])).

fof(f685,plain,(
    ! [X4,X2,X3] : k4_enumset1(X2,X2,X2,X3,X4,X4) = k4_enumset1(X2,X2,X2,X2,X3,X4) ),
    inference(superposition,[],[f133,f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X2,X2,X3))) ),
    inference(definition_unfolding,[],[f114,f117,f120,f119,f119])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f133,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X3,X3,X3))) ),
    inference(definition_unfolding,[],[f115,f117,f120,f118,f121])).

fof(f121,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f119])).

fof(f73,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f115,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f1151,plain,(
    sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,sK5,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6))) ),
    inference(backward_demodulation,[],[f853,f685])).

fof(f853,plain,(
    sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6))) ),
    inference(backward_demodulation,[],[f364,f637])).

fof(f637,plain,(
    ! [X2,X0,X1] : k4_enumset1(X1,X1,X1,X1,X0,X2) = k4_enumset1(X0,X0,X0,X1,X2,X1) ),
    inference(superposition,[],[f132,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X2,X2,X2,X2,X2,X0))) ),
    inference(definition_unfolding,[],[f91,f120,f119,f119,f118])).

fof(f91,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(f364,plain,(
    sK5 != k3_tarski(k4_enumset1(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6))) ),
    inference(forward_demodulation,[],[f122,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f89,f118,f118])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(f122,plain,(
    sK5 != k3_tarski(k4_enumset1(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5)) ),
    inference(definition_unfolding,[],[f70,f120,f119])).

fof(f70,plain,(
    sK5 != k2_xboole_0(k2_tarski(sK4,sK6),sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK5 != k2_xboole_0(k2_tarski(sK4,sK6),sK5)
    & r2_hidden(sK6,sK5)
    & r2_hidden(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK5 != k2_xboole_0(k2_tarski(sK4,sK6),sK5)
      & r2_hidden(sK6,sK5)
      & r2_hidden(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f4112,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ r1_tarski(X0,X2)
      | ~ v1_xboole_0(X1) ) ),
    inference(superposition,[],[f144,f4089])).

fof(f4089,plain,(
    ! [X14,X15] :
      ( k5_xboole_0(X15,X15) = X14
      | ~ v1_xboole_0(X14) ) ),
    inference(subsumption_resolution,[],[f4078,f134])).

fof(f134,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4078,plain,(
    ! [X14,X15] :
      ( k5_xboole_0(X15,X15) = X14
      | ~ v1_xboole_0(X14)
      | ~ r1_tarski(X15,X15) ) ),
    inference(resolution,[],[f4028,f144])).

fof(f4028,plain,(
    ! [X4,X2,X3] :
      ( ~ sP1(X4,X4,X3)
      | X2 = X3
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f4026,f205])).

fof(f205,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X3)
      | X2 = X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(superposition,[],[f127,f127])).

fof(f4026,plain,(
    ! [X0,X1] :
      ( sP1(X0,X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f4014])).

fof(f4014,plain,(
    ! [X0,X1] :
      ( sP1(X0,X0,X1)
      | ~ v1_xboole_0(X1)
      | sP1(X0,X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f1349,f1316])).

fof(f1316,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1,X2),X1)
      | sP1(X0,X1,X2)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f403,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f403,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK10(X3,X4,X5),X5)
      | sP1(X3,X4,X5)
      | ~ r2_hidden(sK10(X3,X4,X5),X4) ) ),
    inference(resolution,[],[f94,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK10(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK10(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK10(X0,X1,X2),X0)
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sP0(X1,sK10(X0,X1,X2),X0)
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK10(X0,X1,X2),X0)
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sP0(X1,sK10(X0,X1,X2),X0)
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f1349,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f404,f74])).

fof(f404,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK10(X6,X7,X8),X8)
      | sP1(X6,X7,X8)
      | r2_hidden(sK10(X6,X7,X8),X6) ) ),
    inference(resolution,[],[f94,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f144,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,k5_xboole_0(X0,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f136,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f136,plain,(
    ! [X0,X1] : sP1(X0,X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f99,f78])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2642,plain,(
    ~ spl12_16 ),
    inference(avatar_contradiction_clause,[],[f2641])).

fof(f2641,plain,
    ( $false
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f2637,f1640])).

fof(f1640,plain,
    ( ! [X0] : r2_hidden(sK7(k1_xboole_0),X0)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f1639])).

fof(f1639,plain,
    ( spl12_16
  <=> ! [X0] : r2_hidden(sK7(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f2637,plain,
    ( ! [X3] : ~ r2_hidden(sK7(k1_xboole_0),X3)
    | ~ spl12_16 ),
    inference(resolution,[],[f2616,f97])).

fof(f2616,plain,
    ( ! [X6,X5] : sP0(X5,sK7(k1_xboole_0),X6)
    | ~ spl12_16 ),
    inference(resolution,[],[f1640,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f92,f136])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1642,plain,
    ( spl12_16
    | spl12_12 ),
    inference(avatar_split_clause,[],[f463,f1621,f1639])).

fof(f463,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | r2_hidden(sK7(k1_xboole_0),X0) ) ),
    inference(resolution,[],[f461,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f461,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X4,X5))
      | v1_xboole_0(X3)
      | r2_hidden(sK7(X3),X5) ) ),
    inference(resolution,[],[f288,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X1,X3,X0] :
      ( sP2(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f288,plain,(
    ! [X4,X2,X3] :
      ( sP2(X4,sK7(X2),X3)
      | ~ r1_tarski(X2,k3_xboole_0(X3,X4))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f254,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | sP2(X2,X0,X1) ) ),
    inference(resolution,[],[f101,f137])).

fof(f137,plain,(
    ! [X0,X1] : sP3(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f35,f34])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,sK11(X0,X1,X2),X0)
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( sP2(X1,sK11(X0,X1,X2),X0)
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,sK11(X0,X1,X2),X0)
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( sP2(X1,sK11(X0,X1,X2),X0)
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X3,X0) )
            & ( sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f254,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK7(X3),X4)
      | v1_xboole_0(X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f245,f83])).

fof(f245,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK7(k3_xboole_0(X2,X3)),X3)
      | v1_xboole_0(k3_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f173,f106])).

fof(f173,plain,(
    ! [X0,X1] :
      ( sP2(X0,sK7(k3_xboole_0(X1,X0)),X1)
      | v1_xboole_0(k3_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f171,f75])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1564,plain,(
    spl12_6 ),
    inference(avatar_contradiction_clause,[],[f1563])).

fof(f1563,plain,
    ( $false
    | spl12_6 ),
    inference(subsumption_resolution,[],[f1562,f68])).

fof(f68,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f1562,plain,
    ( ~ r2_hidden(sK4,sK5)
    | spl12_6 ),
    inference(subsumption_resolution,[],[f1561,f69])).

fof(f69,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f1561,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK4,sK5)
    | spl12_6 ),
    inference(resolution,[],[f1554,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f112,f119])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f1554,plain,
    ( ~ r1_tarski(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5)
    | spl12_6 ),
    inference(avatar_component_clause,[],[f1552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (18126)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (18128)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (18135)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (18151)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (18127)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (18125)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (18125)Refutation not found, incomplete strategy% (18125)------------------------------
% 0.21/0.53  % (18125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18125)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18125)Memory used [KB]: 10746
% 0.21/0.53  % (18125)Time elapsed: 0.111 s
% 0.21/0.53  % (18125)------------------------------
% 0.21/0.53  % (18125)------------------------------
% 0.21/0.53  % (18132)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (18131)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (18154)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (18131)Refutation not found, incomplete strategy% (18131)------------------------------
% 0.21/0.53  % (18131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18145)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (18129)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (18134)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (18131)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18131)Memory used [KB]: 10746
% 0.21/0.53  % (18131)Time elapsed: 0.123 s
% 0.21/0.53  % (18131)------------------------------
% 0.21/0.53  % (18131)------------------------------
% 0.21/0.53  % (18133)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (18134)Refutation not found, incomplete strategy% (18134)------------------------------
% 0.21/0.53  % (18134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18134)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18134)Memory used [KB]: 10618
% 0.21/0.53  % (18134)Time elapsed: 0.127 s
% 0.21/0.53  % (18134)------------------------------
% 0.21/0.53  % (18134)------------------------------
% 0.21/0.54  % (18140)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (18123)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (18123)Refutation not found, incomplete strategy% (18123)------------------------------
% 0.21/0.54  % (18123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18123)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18123)Memory used [KB]: 1663
% 0.21/0.54  % (18123)Time elapsed: 0.125 s
% 0.21/0.54  % (18123)------------------------------
% 0.21/0.54  % (18123)------------------------------
% 0.21/0.54  % (18147)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (18130)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (18150)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (18138)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (18141)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (18143)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (18144)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (18152)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (18143)Refutation not found, incomplete strategy% (18143)------------------------------
% 0.21/0.54  % (18143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18143)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18143)Memory used [KB]: 10746
% 0.21/0.54  % (18143)Time elapsed: 0.137 s
% 0.21/0.54  % (18143)------------------------------
% 0.21/0.54  % (18143)------------------------------
% 0.21/0.54  % (18142)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (18139)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (18146)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (18133)Refutation not found, incomplete strategy% (18133)------------------------------
% 0.21/0.55  % (18133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18148)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (18133)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18133)Memory used [KB]: 10618
% 0.21/0.55  % (18133)Time elapsed: 0.098 s
% 0.21/0.55  % (18133)------------------------------
% 0.21/0.55  % (18133)------------------------------
% 0.21/0.55  % (18137)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (18145)Refutation not found, incomplete strategy% (18145)------------------------------
% 0.21/0.56  % (18145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18124)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (18136)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (18145)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18145)Memory used [KB]: 10746
% 0.21/0.56  % (18145)Time elapsed: 0.149 s
% 0.21/0.56  % (18145)------------------------------
% 0.21/0.56  % (18145)------------------------------
% 1.50/0.56  % (18132)Refutation not found, incomplete strategy% (18132)------------------------------
% 1.50/0.56  % (18132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (18132)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (18132)Memory used [KB]: 10618
% 1.50/0.56  % (18132)Time elapsed: 0.142 s
% 1.50/0.56  % (18132)------------------------------
% 1.50/0.56  % (18132)------------------------------
% 1.50/0.56  % (18144)Refutation not found, incomplete strategy% (18144)------------------------------
% 1.50/0.56  % (18144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (18144)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (18144)Memory used [KB]: 1791
% 1.50/0.56  % (18144)Time elapsed: 0.157 s
% 1.50/0.56  % (18144)------------------------------
% 1.50/0.56  % (18144)------------------------------
% 1.50/0.57  % (18140)Refutation not found, incomplete strategy% (18140)------------------------------
% 1.50/0.57  % (18140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.58  % (18140)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.58  
% 1.70/0.58  % (18140)Memory used [KB]: 10618
% 1.70/0.58  % (18140)Time elapsed: 0.170 s
% 1.70/0.58  % (18140)------------------------------
% 1.70/0.58  % (18140)------------------------------
% 2.13/0.65  % (18246)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.13/0.66  % (18241)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.13/0.66  % (18247)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.13/0.66  % (18241)Refutation not found, incomplete strategy% (18241)------------------------------
% 2.13/0.66  % (18241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.66  % (18241)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.66  
% 2.13/0.66  % (18241)Memory used [KB]: 6140
% 2.13/0.66  % (18241)Time elapsed: 0.101 s
% 2.13/0.66  % (18241)------------------------------
% 2.13/0.66  % (18241)------------------------------
% 2.13/0.66  % (18260)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.13/0.67  % (18253)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.13/0.68  % (18257)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.13/0.69  % (18127)Refutation not found, incomplete strategy% (18127)------------------------------
% 2.13/0.69  % (18127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.69  % (18265)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.13/0.69  % (18259)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.13/0.70  % (18127)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.70  
% 2.13/0.70  % (18127)Memory used [KB]: 7419
% 2.13/0.70  % (18127)Time elapsed: 0.281 s
% 2.13/0.70  % (18127)------------------------------
% 2.13/0.70  % (18127)------------------------------
% 2.13/0.70  % (18262)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.52/0.72  % (18273)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.79/0.80  % (18246)Refutation not found, incomplete strategy% (18246)------------------------------
% 2.79/0.80  % (18246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.79/0.80  % (18290)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.79/0.81  % (18246)Termination reason: Refutation not found, incomplete strategy
% 2.79/0.81  
% 2.79/0.81  % (18246)Memory used [KB]: 6140
% 2.79/0.81  % (18246)Time elapsed: 0.213 s
% 2.79/0.81  % (18246)------------------------------
% 2.79/0.81  % (18246)------------------------------
% 2.79/0.84  % (18304)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 3.22/0.85  % (18128)Time limit reached!
% 3.22/0.85  % (18128)------------------------------
% 3.22/0.85  % (18128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.85  % (18128)Termination reason: Time limit
% 3.22/0.85  % (18128)Termination phase: Saturation
% 3.22/0.85  
% 3.22/0.85  % (18128)Memory used [KB]: 8827
% 3.22/0.85  % (18128)Time elapsed: 0.400 s
% 3.22/0.85  % (18128)------------------------------
% 3.22/0.85  % (18128)------------------------------
% 3.22/0.87  % (18151)Refutation found. Thanks to Tanya!
% 3.22/0.87  % SZS status Theorem for theBenchmark
% 3.22/0.87  % SZS output start Proof for theBenchmark
% 3.22/0.87  fof(f4771,plain,(
% 3.22/0.87    $false),
% 3.22/0.87    inference(avatar_sat_refutation,[],[f1564,f1642,f2642,f4769])).
% 3.22/0.87  fof(f4769,plain,(
% 3.22/0.87    ~spl12_6 | ~spl12_12),
% 3.22/0.87    inference(avatar_contradiction_clause,[],[f4768])).
% 3.22/0.87  fof(f4768,plain,(
% 3.22/0.87    $false | (~spl12_6 | ~spl12_12)),
% 3.22/0.87    inference(subsumption_resolution,[],[f4767,f1623])).
% 3.22/0.87  fof(f1623,plain,(
% 3.22/0.87    v1_xboole_0(k1_xboole_0) | ~spl12_12),
% 3.22/0.87    inference(avatar_component_clause,[],[f1621])).
% 3.22/0.87  fof(f1621,plain,(
% 3.22/0.87    spl12_12 <=> v1_xboole_0(k1_xboole_0)),
% 3.22/0.87    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 3.22/0.87  fof(f4767,plain,(
% 3.22/0.87    ~v1_xboole_0(k1_xboole_0) | ~spl12_6),
% 3.22/0.87    inference(trivial_inequality_removal,[],[f4761])).
% 3.22/0.87  fof(f4761,plain,(
% 3.22/0.87    sK5 != sK5 | ~v1_xboole_0(k1_xboole_0) | ~spl12_6),
% 3.22/0.87    inference(superposition,[],[f4756,f123])).
% 3.22/0.87  fof(f123,plain,(
% 3.22/0.87    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.22/0.87    inference(definition_unfolding,[],[f72,f120])).
% 3.22/0.87  fof(f120,plain,(
% 3.22/0.87    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.22/0.87    inference(definition_unfolding,[],[f76,f119])).
% 3.22/0.87  fof(f119,plain,(
% 3.22/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.22/0.87    inference(definition_unfolding,[],[f77,f118])).
% 3.22/0.87  fof(f118,plain,(
% 3.22/0.87    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.22/0.87    inference(definition_unfolding,[],[f90,f117])).
% 3.22/0.87  fof(f117,plain,(
% 3.22/0.87    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.22/0.87    inference(definition_unfolding,[],[f113,f116])).
% 3.22/0.87  fof(f116,plain,(
% 3.22/0.87    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.22/0.87    inference(cnf_transformation,[],[f19])).
% 3.22/0.87  fof(f19,axiom,(
% 3.22/0.87    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.22/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 3.22/0.87  fof(f113,plain,(
% 3.22/0.87    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.22/0.87    inference(cnf_transformation,[],[f18])).
% 3.22/0.88  fof(f18,axiom,(
% 3.22/0.88    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.22/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 3.22/0.88  fof(f90,plain,(
% 3.22/0.88    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.22/0.88    inference(cnf_transformation,[],[f17])).
% 3.22/0.88  fof(f17,axiom,(
% 3.22/0.88    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.22/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.22/0.88  fof(f77,plain,(
% 3.22/0.88    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.22/0.88    inference(cnf_transformation,[],[f16])).
% 3.22/0.88  fof(f16,axiom,(
% 3.22/0.88    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.22/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.22/0.88  fof(f76,plain,(
% 3.22/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.22/0.88    inference(cnf_transformation,[],[f21])).
% 3.22/0.88  fof(f21,axiom,(
% 3.22/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.22/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.22/0.88  fof(f72,plain,(
% 3.22/0.88    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.22/0.88    inference(cnf_transformation,[],[f8])).
% 3.22/0.88  fof(f8,axiom,(
% 3.22/0.88    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.22/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 3.22/0.88  fof(f4756,plain,(
% 3.22/0.88    ( ! [X23] : (sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,sK5,sK5,X23)) | ~v1_xboole_0(X23)) ) | ~spl12_6),
% 3.22/0.88    inference(subsumption_resolution,[],[f4752,f1553])).
% 3.22/0.88  fof(f1553,plain,(
% 3.22/0.88    r1_tarski(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5) | ~spl12_6),
% 3.22/0.88    inference(avatar_component_clause,[],[f1552])).
% 3.22/0.88  fof(f1552,plain,(
% 3.22/0.88    spl12_6 <=> r1_tarski(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5)),
% 3.22/0.88    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 3.22/0.88  fof(f4752,plain,(
% 3.22/0.88    ( ! [X23] : (~r1_tarski(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5) | ~v1_xboole_0(X23) | sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,sK5,sK5,X23))) )),
% 3.22/0.88    inference(resolution,[],[f4112,f1533])).
% 3.22/0.88  fof(f1533,plain,(
% 3.22/0.88    ( ! [X24] : (~sP1(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5,X24) | sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,sK5,sK5,X24))) )),
% 3.22/0.88    inference(superposition,[],[f1204,f489])).
% 3.22/0.88  fof(f489,plain,(
% 3.22/0.88    ( ! [X2,X0,X1] : (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0)) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) | ~sP1(X0,X1,X2)) )),
% 3.22/0.88    inference(superposition,[],[f124,f127])).
% 3.22/0.88  fof(f127,plain,(
% 3.22/0.88    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~sP1(X0,X1,X2)) )),
% 3.22/0.88    inference(definition_unfolding,[],[f100,f78])).
% 3.22/0.88  fof(f78,plain,(
% 3.22/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.22/0.88    inference(cnf_transformation,[],[f7])).
% 3.22/0.88  fof(f7,axiom,(
% 3.22/0.88    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.22/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.22/0.88  fof(f100,plain,(
% 3.22/0.88    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 3.22/0.88    inference(cnf_transformation,[],[f57])).
% 3.22/0.88  fof(f57,plain,(
% 3.22/0.88    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 3.22/0.88    inference(nnf_transformation,[],[f33])).
% 3.22/0.88  fof(f33,plain,(
% 3.22/0.88    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 3.22/0.88    inference(definition_folding,[],[f3,f32,f31])).
% 3.22/0.88  fof(f31,plain,(
% 3.22/0.88    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 3.22/0.88    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.22/0.88  fof(f32,plain,(
% 3.22/0.88    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 3.22/0.88    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.22/0.88  fof(f3,axiom,(
% 3.22/0.88    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.22/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.22/0.88  fof(f124,plain,(
% 3.22/0.88    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.22/0.88    inference(definition_unfolding,[],[f79,f120,f78,f120])).
% 3.22/0.88  fof(f79,plain,(
% 3.22/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.22/0.88    inference(cnf_transformation,[],[f11])).
% 3.22/0.88  fof(f11,axiom,(
% 3.22/0.88    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.22/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.22/0.88  fof(f1204,plain,(
% 3.22/0.88    sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,sK5,sK5,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6)))),
% 3.22/0.88    inference(forward_demodulation,[],[f1151,f685])).
% 3.22/0.88  fof(f685,plain,(
% 3.22/0.88    ( ! [X4,X2,X3] : (k4_enumset1(X2,X2,X2,X3,X4,X4) = k4_enumset1(X2,X2,X2,X2,X3,X4)) )),
% 3.22/0.88    inference(superposition,[],[f133,f132])).
% 3.22/0.88  fof(f132,plain,(
% 3.22/0.88    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X2,X2,X3)))) )),
% 3.22/0.88    inference(definition_unfolding,[],[f114,f117,f120,f119,f119])).
% 3.22/0.88  fof(f114,plain,(
% 3.22/0.88    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.22/0.88    inference(cnf_transformation,[],[f12])).
% 3.41/0.88  fof(f12,axiom,(
% 3.41/0.88    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 3.41/0.88  fof(f133,plain,(
% 3.41/0.88    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X3,X3,X3)))) )),
% 3.41/0.88    inference(definition_unfolding,[],[f115,f117,f120,f118,f121])).
% 3.41/0.88  fof(f121,plain,(
% 3.41/0.88    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 3.41/0.88    inference(definition_unfolding,[],[f73,f119])).
% 3.41/0.88  fof(f73,plain,(
% 3.41/0.88    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f15])).
% 3.41/0.88  fof(f15,axiom,(
% 3.41/0.88    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.41/0.88  fof(f115,plain,(
% 3.41/0.88    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 3.41/0.88    inference(cnf_transformation,[],[f14])).
% 3.41/0.88  fof(f14,axiom,(
% 3.41/0.88    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 3.41/0.88  fof(f1151,plain,(
% 3.41/0.88    sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,sK5,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6)))),
% 3.41/0.88    inference(backward_demodulation,[],[f853,f685])).
% 3.41/0.88  fof(f853,plain,(
% 3.41/0.88    sK5 != k3_tarski(k4_enumset1(sK5,sK5,sK5,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6)))),
% 3.41/0.88    inference(backward_demodulation,[],[f364,f637])).
% 3.41/0.88  fof(f637,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (k4_enumset1(X1,X1,X1,X1,X0,X2) = k4_enumset1(X0,X0,X0,X1,X2,X1)) )),
% 3.41/0.88    inference(superposition,[],[f132,f126])).
% 3.41/0.88  fof(f126,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X2,X2,X2,X2,X2,X0)))) )),
% 3.41/0.88    inference(definition_unfolding,[],[f91,f120,f119,f119,f118])).
% 3.41/0.88  fof(f91,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f13])).
% 3.41/0.88  fof(f13,axiom,(
% 3.41/0.88    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 3.41/0.88  fof(f364,plain,(
% 3.41/0.88    sK5 != k3_tarski(k4_enumset1(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5,k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6)))),
% 3.41/0.88    inference(forward_demodulation,[],[f122,f125])).
% 3.41/0.88  fof(f125,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X2,X1)) )),
% 3.41/0.88    inference(definition_unfolding,[],[f89,f118,f118])).
% 3.41/0.88  fof(f89,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f20])).
% 3.41/0.88  fof(f20,axiom,(
% 3.41/0.88    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).
% 3.41/0.88  fof(f122,plain,(
% 3.41/0.88    sK5 != k3_tarski(k4_enumset1(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5))),
% 3.41/0.88    inference(definition_unfolding,[],[f70,f120,f119])).
% 3.41/0.88  fof(f70,plain,(
% 3.41/0.88    sK5 != k2_xboole_0(k2_tarski(sK4,sK6),sK5)),
% 3.41/0.88    inference(cnf_transformation,[],[f38])).
% 3.41/0.88  fof(f38,plain,(
% 3.41/0.88    sK5 != k2_xboole_0(k2_tarski(sK4,sK6),sK5) & r2_hidden(sK6,sK5) & r2_hidden(sK4,sK5)),
% 3.41/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f37])).
% 3.41/0.88  fof(f37,plain,(
% 3.41/0.88    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK5 != k2_xboole_0(k2_tarski(sK4,sK6),sK5) & r2_hidden(sK6,sK5) & r2_hidden(sK4,sK5))),
% 3.41/0.88    introduced(choice_axiom,[])).
% 3.41/0.88  fof(f27,plain,(
% 3.41/0.88    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 3.41/0.88    inference(flattening,[],[f26])).
% 3.41/0.88  fof(f26,plain,(
% 3.41/0.88    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 3.41/0.88    inference(ennf_transformation,[],[f24])).
% 3.41/0.88  fof(f24,negated_conjecture,(
% 3.41/0.88    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 3.41/0.88    inference(negated_conjecture,[],[f23])).
% 3.41/0.88  fof(f23,conjecture,(
% 3.41/0.88    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 3.41/0.88  fof(f4112,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~r1_tarski(X0,X2) | ~v1_xboole_0(X1)) )),
% 3.41/0.88    inference(superposition,[],[f144,f4089])).
% 3.41/0.88  fof(f4089,plain,(
% 3.41/0.88    ( ! [X14,X15] : (k5_xboole_0(X15,X15) = X14 | ~v1_xboole_0(X14)) )),
% 3.41/0.88    inference(subsumption_resolution,[],[f4078,f134])).
% 3.41/0.88  fof(f134,plain,(
% 3.41/0.88    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.41/0.88    inference(equality_resolution,[],[f87])).
% 3.41/0.88  fof(f87,plain,(
% 3.41/0.88    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.41/0.88    inference(cnf_transformation,[],[f49])).
% 3.41/0.88  fof(f49,plain,(
% 3.41/0.88    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.41/0.88    inference(flattening,[],[f48])).
% 3.41/0.88  fof(f48,plain,(
% 3.41/0.88    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.41/0.88    inference(nnf_transformation,[],[f6])).
% 3.41/0.88  fof(f6,axiom,(
% 3.41/0.88    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.41/0.88  fof(f4078,plain,(
% 3.41/0.88    ( ! [X14,X15] : (k5_xboole_0(X15,X15) = X14 | ~v1_xboole_0(X14) | ~r1_tarski(X15,X15)) )),
% 3.41/0.88    inference(resolution,[],[f4028,f144])).
% 3.41/0.88  fof(f4028,plain,(
% 3.41/0.88    ( ! [X4,X2,X3] : (~sP1(X4,X4,X3) | X2 = X3 | ~v1_xboole_0(X2)) )),
% 3.41/0.88    inference(resolution,[],[f4026,f205])).
% 3.41/0.88  fof(f205,plain,(
% 3.41/0.88    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X3) | X2 = X3 | ~sP1(X0,X1,X2)) )),
% 3.41/0.88    inference(superposition,[],[f127,f127])).
% 3.41/0.88  fof(f4026,plain,(
% 3.41/0.88    ( ! [X0,X1] : (sP1(X0,X0,X1) | ~v1_xboole_0(X1)) )),
% 3.41/0.88    inference(duplicate_literal_removal,[],[f4014])).
% 3.41/0.88  fof(f4014,plain,(
% 3.41/0.88    ( ! [X0,X1] : (sP1(X0,X0,X1) | ~v1_xboole_0(X1) | sP1(X0,X0,X1) | ~v1_xboole_0(X1)) )),
% 3.41/0.88    inference(resolution,[],[f1349,f1316])).
% 3.41/0.88  fof(f1316,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (~r2_hidden(sK10(X0,X1,X2),X1) | sP1(X0,X1,X2) | ~v1_xboole_0(X2)) )),
% 3.41/0.88    inference(resolution,[],[f403,f74])).
% 3.41/0.88  fof(f74,plain,(
% 3.41/0.88    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f42])).
% 3.41/0.88  fof(f42,plain,(
% 3.41/0.88    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.41/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).
% 3.41/0.88  fof(f41,plain,(
% 3.41/0.88    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 3.41/0.88    introduced(choice_axiom,[])).
% 3.41/0.88  fof(f40,plain,(
% 3.41/0.88    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.41/0.88    inference(rectify,[],[f39])).
% 3.41/0.88  fof(f39,plain,(
% 3.41/0.88    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.41/0.88    inference(nnf_transformation,[],[f1])).
% 3.41/0.88  fof(f1,axiom,(
% 3.41/0.88    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 3.41/0.88  fof(f403,plain,(
% 3.41/0.88    ( ! [X4,X5,X3] : (r2_hidden(sK10(X3,X4,X5),X5) | sP1(X3,X4,X5) | ~r2_hidden(sK10(X3,X4,X5),X4)) )),
% 3.41/0.88    inference(resolution,[],[f94,f97])).
% 3.41/0.88  fof(f97,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f56])).
% 3.41/0.88  fof(f56,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 3.41/0.88    inference(rectify,[],[f55])).
% 3.41/0.88  fof(f55,plain,(
% 3.41/0.88    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 3.41/0.88    inference(flattening,[],[f54])).
% 3.41/0.88  fof(f54,plain,(
% 3.41/0.88    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 3.41/0.88    inference(nnf_transformation,[],[f31])).
% 3.41/0.88  fof(f94,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (sP0(X1,sK10(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK10(X0,X1,X2),X2)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f53])).
% 3.41/0.88  fof(f53,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK10(X0,X1,X2),X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP0(X1,sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 3.41/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f51,f52])).
% 3.41/0.88  fof(f52,plain,(
% 3.41/0.88    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK10(X0,X1,X2),X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP0(X1,sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 3.41/0.88    introduced(choice_axiom,[])).
% 3.41/0.88  fof(f51,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 3.41/0.88    inference(rectify,[],[f50])).
% 3.41/0.88  fof(f50,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 3.41/0.88    inference(nnf_transformation,[],[f32])).
% 3.41/0.88  fof(f1349,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X0) | sP1(X0,X1,X2) | ~v1_xboole_0(X2)) )),
% 3.41/0.88    inference(resolution,[],[f404,f74])).
% 3.41/0.88  fof(f404,plain,(
% 3.41/0.88    ( ! [X6,X8,X7] : (r2_hidden(sK10(X6,X7,X8),X8) | sP1(X6,X7,X8) | r2_hidden(sK10(X6,X7,X8),X6)) )),
% 3.41/0.88    inference(resolution,[],[f94,f96])).
% 3.41/0.88  fof(f96,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f56])).
% 3.41/0.88  fof(f144,plain,(
% 3.41/0.88    ( ! [X0,X1] : (sP1(X0,X1,k5_xboole_0(X0,X0)) | ~r1_tarski(X0,X1)) )),
% 3.41/0.88    inference(superposition,[],[f136,f83])).
% 3.41/0.88  fof(f83,plain,(
% 3.41/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f29])).
% 3.41/0.88  fof(f29,plain,(
% 3.41/0.88    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.41/0.88    inference(ennf_transformation,[],[f9])).
% 3.41/0.88  fof(f9,axiom,(
% 3.41/0.88    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.41/0.88  fof(f136,plain,(
% 3.41/0.88    ( ! [X0,X1] : (sP1(X0,X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.41/0.88    inference(equality_resolution,[],[f128])).
% 3.41/0.88  fof(f128,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.41/0.88    inference(definition_unfolding,[],[f99,f78])).
% 3.41/0.88  fof(f99,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.41/0.88    inference(cnf_transformation,[],[f57])).
% 3.41/0.88  fof(f2642,plain,(
% 3.41/0.88    ~spl12_16),
% 3.41/0.88    inference(avatar_contradiction_clause,[],[f2641])).
% 3.41/0.88  fof(f2641,plain,(
% 3.41/0.88    $false | ~spl12_16),
% 3.41/0.88    inference(subsumption_resolution,[],[f2637,f1640])).
% 3.41/0.88  fof(f1640,plain,(
% 3.41/0.88    ( ! [X0] : (r2_hidden(sK7(k1_xboole_0),X0)) ) | ~spl12_16),
% 3.41/0.88    inference(avatar_component_clause,[],[f1639])).
% 3.41/0.88  fof(f1639,plain,(
% 3.41/0.88    spl12_16 <=> ! [X0] : r2_hidden(sK7(k1_xboole_0),X0)),
% 3.41/0.88    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).
% 3.41/0.88  fof(f2637,plain,(
% 3.41/0.88    ( ! [X3] : (~r2_hidden(sK7(k1_xboole_0),X3)) ) | ~spl12_16),
% 3.41/0.88    inference(resolution,[],[f2616,f97])).
% 3.41/0.88  fof(f2616,plain,(
% 3.41/0.88    ( ! [X6,X5] : (sP0(X5,sK7(k1_xboole_0),X6)) ) | ~spl12_16),
% 3.41/0.88    inference(resolution,[],[f1640,f162])).
% 3.41/0.88  fof(f162,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | sP0(X2,X0,X1)) )),
% 3.41/0.88    inference(resolution,[],[f92,f136])).
% 3.41/0.88  fof(f92,plain,(
% 3.41/0.88    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f53])).
% 3.41/0.88  fof(f1642,plain,(
% 3.41/0.88    spl12_16 | spl12_12),
% 3.41/0.88    inference(avatar_split_clause,[],[f463,f1621,f1639])).
% 3.41/0.88  fof(f463,plain,(
% 3.41/0.88    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | r2_hidden(sK7(k1_xboole_0),X0)) )),
% 3.41/0.88    inference(resolution,[],[f461,f71])).
% 3.41/0.88  fof(f71,plain,(
% 3.41/0.88    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f10])).
% 3.41/0.88  fof(f10,axiom,(
% 3.41/0.88    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.41/0.88  fof(f461,plain,(
% 3.41/0.88    ( ! [X4,X5,X3] : (~r1_tarski(X3,k3_xboole_0(X4,X5)) | v1_xboole_0(X3) | r2_hidden(sK7(X3),X5)) )),
% 3.41/0.88    inference(resolution,[],[f288,f106])).
% 3.41/0.88  fof(f106,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f64])).
% 3.41/0.88  fof(f64,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP2(X0,X1,X2)))),
% 3.41/0.88    inference(rectify,[],[f63])).
% 3.41/0.88  fof(f63,plain,(
% 3.41/0.88    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 3.41/0.88    inference(flattening,[],[f62])).
% 3.41/0.88  fof(f62,plain,(
% 3.41/0.88    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 3.41/0.88    inference(nnf_transformation,[],[f34])).
% 3.41/0.88  fof(f34,plain,(
% 3.41/0.88    ! [X1,X3,X0] : (sP2(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 3.41/0.88    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 3.41/0.88  fof(f288,plain,(
% 3.41/0.88    ( ! [X4,X2,X3] : (sP2(X4,sK7(X2),X3) | ~r1_tarski(X2,k3_xboole_0(X3,X4)) | v1_xboole_0(X2)) )),
% 3.41/0.88    inference(resolution,[],[f254,f171])).
% 3.41/0.88  fof(f171,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | sP2(X2,X0,X1)) )),
% 3.41/0.88    inference(resolution,[],[f101,f137])).
% 3.41/0.88  fof(f137,plain,(
% 3.41/0.88    ( ! [X0,X1] : (sP3(X0,X1,k3_xboole_0(X0,X1))) )),
% 3.41/0.88    inference(equality_resolution,[],[f108])).
% 3.41/0.88  fof(f108,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.41/0.88    inference(cnf_transformation,[],[f65])).
% 3.41/0.88  fof(f65,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) & (sP3(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 3.41/0.88    inference(nnf_transformation,[],[f36])).
% 3.41/0.88  fof(f36,plain,(
% 3.41/0.88    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP3(X0,X1,X2))),
% 3.41/0.88    inference(definition_folding,[],[f2,f35,f34])).
% 3.41/0.88  fof(f35,plain,(
% 3.41/0.88    ! [X0,X1,X2] : (sP3(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP2(X1,X3,X0)))),
% 3.41/0.88    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 3.41/0.88  fof(f2,axiom,(
% 3.41/0.88    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 3.41/0.88  fof(f101,plain,(
% 3.41/0.88    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | sP2(X1,X4,X0)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f61])).
% 3.41/0.88  fof(f61,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ((~sP2(X1,sK11(X0,X1,X2),X0) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (sP2(X1,sK11(X0,X1,X2),X0) | r2_hidden(sK11(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 3.41/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f59,f60])).
% 3.41/0.88  fof(f60,plain,(
% 3.41/0.88    ! [X2,X1,X0] : (? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP2(X1,sK11(X0,X1,X2),X0) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (sP2(X1,sK11(X0,X1,X2),X0) | r2_hidden(sK11(X0,X1,X2),X2))))),
% 3.41/0.88    introduced(choice_axiom,[])).
% 3.41/0.88  fof(f59,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 3.41/0.88    inference(rectify,[],[f58])).
% 3.41/0.88  fof(f58,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP2(X1,X3,X0)) & (sP2(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP3(X0,X1,X2)))),
% 3.41/0.88    inference(nnf_transformation,[],[f35])).
% 3.41/0.88  fof(f254,plain,(
% 3.41/0.88    ( ! [X4,X3] : (r2_hidden(sK7(X3),X4) | v1_xboole_0(X3) | ~r1_tarski(X3,X4)) )),
% 3.41/0.88    inference(superposition,[],[f245,f83])).
% 3.41/0.88  fof(f245,plain,(
% 3.41/0.88    ( ! [X2,X3] : (r2_hidden(sK7(k3_xboole_0(X2,X3)),X3) | v1_xboole_0(k3_xboole_0(X2,X3))) )),
% 3.41/0.88    inference(resolution,[],[f173,f106])).
% 3.41/0.88  fof(f173,plain,(
% 3.41/0.88    ( ! [X0,X1] : (sP2(X0,sK7(k3_xboole_0(X1,X0)),X1) | v1_xboole_0(k3_xboole_0(X1,X0))) )),
% 3.41/0.88    inference(resolution,[],[f171,f75])).
% 3.41/0.88  fof(f75,plain,(
% 3.41/0.88    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f42])).
% 3.41/0.88  fof(f1564,plain,(
% 3.41/0.88    spl12_6),
% 3.41/0.88    inference(avatar_contradiction_clause,[],[f1563])).
% 3.41/0.88  fof(f1563,plain,(
% 3.41/0.88    $false | spl12_6),
% 3.41/0.88    inference(subsumption_resolution,[],[f1562,f68])).
% 3.41/0.88  fof(f68,plain,(
% 3.41/0.88    r2_hidden(sK4,sK5)),
% 3.41/0.88    inference(cnf_transformation,[],[f38])).
% 3.41/0.88  fof(f1562,plain,(
% 3.41/0.88    ~r2_hidden(sK4,sK5) | spl12_6),
% 3.41/0.88    inference(subsumption_resolution,[],[f1561,f69])).
% 3.41/0.88  fof(f69,plain,(
% 3.41/0.88    r2_hidden(sK6,sK5)),
% 3.41/0.88    inference(cnf_transformation,[],[f38])).
% 3.41/0.88  fof(f1561,plain,(
% 3.41/0.88    ~r2_hidden(sK6,sK5) | ~r2_hidden(sK4,sK5) | spl12_6),
% 3.41/0.88    inference(resolution,[],[f1554,f129])).
% 3.41/0.88  fof(f129,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.41/0.88    inference(definition_unfolding,[],[f112,f119])).
% 3.41/0.88  fof(f112,plain,(
% 3.41/0.88    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.41/0.88    inference(cnf_transformation,[],[f67])).
% 3.41/0.88  fof(f67,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.41/0.88    inference(flattening,[],[f66])).
% 3.41/0.88  fof(f66,plain,(
% 3.41/0.88    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.41/0.88    inference(nnf_transformation,[],[f22])).
% 3.41/0.88  fof(f22,axiom,(
% 3.41/0.88    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.41/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 3.41/0.88  fof(f1554,plain,(
% 3.41/0.88    ~r1_tarski(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK6),sK5) | spl12_6),
% 3.41/0.88    inference(avatar_component_clause,[],[f1552])).
% 3.41/0.88  % SZS output end Proof for theBenchmark
% 3.41/0.88  % (18151)------------------------------
% 3.41/0.88  % (18151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.41/0.88  % (18151)Termination reason: Refutation
% 3.41/0.88  
% 3.41/0.88  % (18151)Memory used [KB]: 8059
% 3.41/0.88  % (18151)Time elapsed: 0.473 s
% 3.41/0.88  % (18151)------------------------------
% 3.41/0.88  % (18151)------------------------------
% 3.41/0.89  % (18119)Success in time 0.518 s
%------------------------------------------------------------------------------
