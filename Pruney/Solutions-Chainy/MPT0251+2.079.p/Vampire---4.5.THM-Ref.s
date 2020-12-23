%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:46 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 493 expanded)
%              Number of leaves         :   20 ( 139 expanded)
%              Depth                    :   26
%              Number of atoms          :  226 (1175 expanded)
%              Number of equality atoms :   66 ( 294 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(subsumption_resolution,[],[f576,f39])).

fof(f39,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f576,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f573])).

fof(f573,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f570,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f61,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f570,plain,(
    ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f569])).

fof(f569,plain,
    ( sK2 != sK2
    | ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(superposition,[],[f270,f527])).

fof(f527,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f526,f75])).

fof(f75,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f42,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f526,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f277,f387])).

fof(f387,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f377,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f377,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f373,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f373,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f372,f194])).

fof(f194,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f74,f193])).

fof(f193,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0) ),
    inference(resolution,[],[f186,f153])).

fof(f153,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(resolution,[],[f152,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f152,plain,(
    ! [X2,X3] : ~ r2_hidden(X2,k3_xboole_0(X3,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f150,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f63,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sP0(k3_xboole_0(X0,k1_xboole_0),X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f66,f74])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP0(X2,X0,X1) )
      & ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f23,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f150,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k3_xboole_0(X3,k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k3_xboole_0(X3,k1_xboole_0))
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f65,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ sP0(k3_xboole_0(X0,k1_xboole_0),X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f67,f74])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f132,f83])).

fof(f132,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | ~ r1_tarski(X1,k1_xboole_0)
      | X1 = X2 ) ),
    inference(resolution,[],[f112,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f107,f56])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f103,f51])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f109,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f372,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(subsumption_resolution,[],[f354,f200])).

fof(f200,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f153,f193])).

fof(f354,plain,(
    ! [X0] :
      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f338,f51])).

fof(f338,plain,(
    ! [X7] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)) = k5_xboole_0(X7,k3_xboole_0(X7,X7)) ),
    inference(superposition,[],[f77,f267])).

fof(f267,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f76,f75])).

fof(f76,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f44,f71,f71])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f48,f47,f47,f71])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f277,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f78,f51])).

fof(f78,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f49,f71,f71,f47])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f270,plain,(
    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f73,f76])).

fof(f73,plain,(
    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f40,f71,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.30/0.57  % (28120)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.57  % (28123)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.57  % (28133)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.52/0.57  % (28127)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.52/0.57  % (28119)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.57  % (28136)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.58  % (28125)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.58  % (28128)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.52/0.58  % (28133)Refutation not found, incomplete strategy% (28133)------------------------------
% 1.52/0.58  % (28133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (28117)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.52/0.58  % (28131)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.52/0.59  % (28139)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.52/0.59  % (28115)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.52/0.59  % (28135)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.59  % (28138)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.59  % (28122)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.52/0.59  % (28137)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.52/0.60  % (28111)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.52/0.60  % (28133)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.60  
% 1.52/0.60  % (28133)Memory used [KB]: 10746
% 1.52/0.60  % (28133)Time elapsed: 0.149 s
% 1.52/0.60  % (28133)------------------------------
% 1.52/0.60  % (28133)------------------------------
% 1.52/0.60  % (28114)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.52/0.60  % (28129)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.52/0.60  % (28132)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.52/0.60  % (28126)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.52/0.61  % (28116)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.52/0.61  % (28140)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.61  % (28118)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.52/0.62  % (28113)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.52/0.62  % (28130)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.52/0.62  % (28124)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.62  % (28134)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.52/0.62  % (28121)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.52/0.62  % (28121)Refutation not found, incomplete strategy% (28121)------------------------------
% 1.52/0.62  % (28121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.62  % (28121)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.62  
% 1.52/0.62  % (28121)Memory used [KB]: 10618
% 1.52/0.62  % (28121)Time elapsed: 0.201 s
% 1.52/0.62  % (28121)------------------------------
% 1.52/0.62  % (28121)------------------------------
% 1.52/0.62  % (28138)Refutation found. Thanks to Tanya!
% 1.52/0.62  % SZS status Theorem for theBenchmark
% 1.52/0.62  % SZS output start Proof for theBenchmark
% 1.52/0.62  fof(f577,plain,(
% 1.52/0.62    $false),
% 1.52/0.62    inference(subsumption_resolution,[],[f576,f39])).
% 1.52/0.62  fof(f39,plain,(
% 1.52/0.62    r2_hidden(sK1,sK2)),
% 1.52/0.62    inference(cnf_transformation,[],[f27])).
% 1.52/0.62  fof(f27,plain,(
% 1.52/0.62    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2)),
% 1.52/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).
% 1.52/0.62  fof(f26,plain,(
% 1.52/0.62    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2))),
% 1.52/0.62    introduced(choice_axiom,[])).
% 1.52/0.62  fof(f20,plain,(
% 1.52/0.62    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.52/0.62    inference(ennf_transformation,[],[f19])).
% 1.52/0.62  fof(f19,negated_conjecture,(
% 1.52/0.62    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.52/0.62    inference(negated_conjecture,[],[f18])).
% 1.52/0.62  fof(f18,conjecture,(
% 1.52/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.52/0.62  fof(f576,plain,(
% 1.52/0.62    ~r2_hidden(sK1,sK2)),
% 1.52/0.62    inference(duplicate_literal_removal,[],[f573])).
% 1.52/0.62  fof(f573,plain,(
% 1.52/0.62    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 1.52/0.62    inference(resolution,[],[f570,f80])).
% 1.52/0.62  fof(f80,plain,(
% 1.52/0.62    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.52/0.62    inference(definition_unfolding,[],[f61,f70])).
% 1.52/0.62  fof(f70,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.52/0.62    inference(definition_unfolding,[],[f46,f69])).
% 1.52/0.62  fof(f69,plain,(
% 1.52/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.52/0.62    inference(definition_unfolding,[],[f58,f68])).
% 1.52/0.62  fof(f68,plain,(
% 1.52/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f15])).
% 1.52/0.62  fof(f15,axiom,(
% 1.52/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.52/0.62  fof(f58,plain,(
% 1.52/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f14])).
% 1.52/0.62  fof(f14,axiom,(
% 1.52/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.52/0.62  fof(f46,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f13])).
% 1.52/0.62  fof(f13,axiom,(
% 1.52/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.52/0.62  fof(f61,plain,(
% 1.52/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f35])).
% 1.52/0.62  fof(f35,plain,(
% 1.52/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.52/0.62    inference(flattening,[],[f34])).
% 1.52/0.62  fof(f34,plain,(
% 1.52/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.52/0.62    inference(nnf_transformation,[],[f17])).
% 1.52/0.62  fof(f17,axiom,(
% 1.52/0.62    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.52/0.62  fof(f570,plain,(
% 1.52/0.62    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.52/0.62    inference(trivial_inequality_removal,[],[f569])).
% 1.52/0.62  fof(f569,plain,(
% 1.52/0.62    sK2 != sK2 | ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.52/0.62    inference(superposition,[],[f270,f527])).
% 1.52/0.62  fof(f527,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.52/0.62    inference(forward_demodulation,[],[f526,f75])).
% 1.52/0.62  fof(f75,plain,(
% 1.52/0.62    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.52/0.62    inference(definition_unfolding,[],[f42,f71])).
% 1.52/0.62  fof(f71,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.52/0.62    inference(definition_unfolding,[],[f45,f70])).
% 1.52/0.62  fof(f45,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.52/0.62    inference(cnf_transformation,[],[f16])).
% 1.52/0.62  fof(f16,axiom,(
% 1.52/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.52/0.62  fof(f42,plain,(
% 1.52/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.62    inference(cnf_transformation,[],[f6])).
% 1.52/0.62  fof(f6,axiom,(
% 1.52/0.62    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.52/0.62  fof(f526,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) | ~r1_tarski(X0,X1)) )),
% 1.52/0.62    inference(forward_demodulation,[],[f277,f387])).
% 1.52/0.62  fof(f387,plain,(
% 1.52/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.52/0.62    inference(subsumption_resolution,[],[f377,f83])).
% 1.52/0.62  fof(f83,plain,(
% 1.52/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.52/0.62    inference(equality_resolution,[],[f53])).
% 1.52/0.62  fof(f53,plain,(
% 1.52/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.52/0.62    inference(cnf_transformation,[],[f29])).
% 1.52/0.62  fof(f29,plain,(
% 1.52/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.62    inference(flattening,[],[f28])).
% 1.52/0.62  fof(f28,plain,(
% 1.52/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.62    inference(nnf_transformation,[],[f4])).
% 1.52/0.62  fof(f4,axiom,(
% 1.52/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.62  fof(f377,plain,(
% 1.52/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 1.52/0.62    inference(superposition,[],[f373,f51])).
% 1.52/0.62  fof(f51,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f21])).
% 1.52/0.62  fof(f21,plain,(
% 1.52/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.52/0.62    inference(ennf_transformation,[],[f7])).
% 1.52/0.62  fof(f7,axiom,(
% 1.52/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.52/0.62  fof(f373,plain,(
% 1.52/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.52/0.62    inference(forward_demodulation,[],[f372,f194])).
% 1.52/0.62  fof(f194,plain,(
% 1.52/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.62    inference(backward_demodulation,[],[f74,f193])).
% 1.52/0.62  fof(f193,plain,(
% 1.52/0.62    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0)) )),
% 1.52/0.62    inference(resolution,[],[f186,f153])).
% 1.52/0.62  fof(f153,plain,(
% 1.52/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 1.52/0.62    inference(resolution,[],[f152,f56])).
% 1.52/0.62  fof(f56,plain,(
% 1.52/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f33])).
% 1.52/0.62  fof(f33,plain,(
% 1.52/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.52/0.62  fof(f32,plain,(
% 1.52/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.52/0.62    introduced(choice_axiom,[])).
% 1.52/0.62  fof(f31,plain,(
% 1.52/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.62    inference(rectify,[],[f30])).
% 1.52/0.62  fof(f30,plain,(
% 1.52/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.62    inference(nnf_transformation,[],[f22])).
% 1.52/0.62  fof(f22,plain,(
% 1.52/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.62    inference(ennf_transformation,[],[f2])).
% 1.52/0.62  fof(f2,axiom,(
% 1.52/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.62  fof(f152,plain,(
% 1.52/0.62    ( ! [X2,X3] : (~r2_hidden(X2,k3_xboole_0(X3,k1_xboole_0))) )),
% 1.52/0.62    inference(subsumption_resolution,[],[f150,f103])).
% 1.52/0.62  fof(f103,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) | ~r2_hidden(X0,X1)) )),
% 1.52/0.62    inference(duplicate_literal_removal,[],[f102])).
% 1.52/0.62  fof(f102,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) | ~r2_hidden(X0,X1)) )),
% 1.52/0.62    inference(resolution,[],[f63,f92])).
% 1.52/0.62  fof(f92,plain,(
% 1.52/0.62    ( ! [X0,X1] : (sP0(k3_xboole_0(X0,k1_xboole_0),X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.52/0.62    inference(superposition,[],[f66,f74])).
% 1.52/0.62  fof(f66,plain,(
% 1.52/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f38])).
% 1.52/0.62  fof(f38,plain,(
% 1.52/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.52/0.62    inference(nnf_transformation,[],[f25])).
% 1.52/0.62  fof(f25,plain,(
% 1.52/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 1.52/0.62    inference(definition_folding,[],[f23,f24])).
% 1.52/0.62  fof(f24,plain,(
% 1.52/0.62    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.52/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.52/0.62  fof(f23,plain,(
% 1.52/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.52/0.62    inference(ennf_transformation,[],[f3])).
% 1.52/0.62  fof(f3,axiom,(
% 1.52/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.52/0.62  fof(f63,plain,(
% 1.52/0.62    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f37])).
% 1.52/0.62  fof(f37,plain,(
% 1.52/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 1.52/0.62    inference(rectify,[],[f36])).
% 1.52/0.62  fof(f36,plain,(
% 1.52/0.62    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 1.52/0.62    inference(nnf_transformation,[],[f24])).
% 1.52/0.62  fof(f150,plain,(
% 1.52/0.62    ( ! [X2,X3] : (r2_hidden(X2,X3) | ~r2_hidden(X2,k3_xboole_0(X3,k1_xboole_0))) )),
% 1.52/0.62    inference(duplicate_literal_removal,[],[f144])).
% 1.52/0.62  fof(f144,plain,(
% 1.52/0.62    ( ! [X2,X3] : (r2_hidden(X2,X3) | ~r2_hidden(X2,k3_xboole_0(X3,k1_xboole_0)) | r2_hidden(X2,X3)) )),
% 1.52/0.62    inference(resolution,[],[f65,f96])).
% 1.52/0.62  fof(f96,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~sP0(k3_xboole_0(X0,k1_xboole_0),X1,X0) | r2_hidden(X1,X0)) )),
% 1.52/0.62    inference(superposition,[],[f67,f74])).
% 1.52/0.62  fof(f67,plain,(
% 1.52/0.62    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f38])).
% 1.52/0.62  fof(f65,plain,(
% 1.52/0.62    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f37])).
% 1.52/0.62  fof(f186,plain,(
% 1.52/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.52/0.62    inference(resolution,[],[f132,f83])).
% 1.52/0.62  fof(f132,plain,(
% 1.52/0.62    ( ! [X2,X1] : (~r1_tarski(X2,k1_xboole_0) | ~r1_tarski(X1,k1_xboole_0) | X1 = X2) )),
% 1.52/0.62    inference(resolution,[],[f112,f109])).
% 1.52/0.62  fof(f109,plain,(
% 1.52/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.52/0.62    inference(resolution,[],[f107,f56])).
% 1.52/0.62  fof(f107,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.52/0.62    inference(duplicate_literal_removal,[],[f106])).
% 1.52/0.62  fof(f106,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.52/0.62    inference(superposition,[],[f103,f51])).
% 1.52/0.62  fof(f112,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.52/0.62    inference(resolution,[],[f109,f54])).
% 1.52/0.62  fof(f54,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f29])).
% 1.52/0.62  fof(f74,plain,(
% 1.52/0.62    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.52/0.62    inference(definition_unfolding,[],[f41,f47])).
% 1.52/0.62  fof(f47,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.52/0.62    inference(cnf_transformation,[],[f5])).
% 1.52/0.62  fof(f5,axiom,(
% 1.52/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.52/0.62  fof(f41,plain,(
% 1.52/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.62    inference(cnf_transformation,[],[f9])).
% 1.52/0.62  fof(f9,axiom,(
% 1.52/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.52/0.62  fof(f372,plain,(
% 1.52/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.52/0.62    inference(subsumption_resolution,[],[f354,f200])).
% 1.52/0.62  fof(f200,plain,(
% 1.52/0.62    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.52/0.62    inference(backward_demodulation,[],[f153,f193])).
% 1.52/0.62  fof(f354,plain,(
% 1.52/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.52/0.62    inference(superposition,[],[f338,f51])).
% 1.52/0.62  fof(f338,plain,(
% 1.52/0.62    ( ! [X7] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)) = k5_xboole_0(X7,k3_xboole_0(X7,X7))) )),
% 1.52/0.62    inference(superposition,[],[f77,f267])).
% 1.52/0.62  fof(f267,plain,(
% 1.52/0.62    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.52/0.62    inference(superposition,[],[f76,f75])).
% 1.52/0.62  fof(f76,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 1.52/0.62    inference(definition_unfolding,[],[f44,f71,f71])).
% 1.52/0.62  fof(f44,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f1])).
% 1.52/0.62  fof(f1,axiom,(
% 1.52/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.52/0.62  fof(f77,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.52/0.62    inference(definition_unfolding,[],[f48,f47,f47,f71])).
% 1.52/0.62  fof(f48,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f10])).
% 1.52/0.62  fof(f10,axiom,(
% 1.52/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.52/0.62  fof(f277,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0))) | ~r1_tarski(X0,X1)) )),
% 1.52/0.62    inference(superposition,[],[f78,f51])).
% 1.52/0.62  fof(f78,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.52/0.62    inference(definition_unfolding,[],[f49,f71,f71,f47])).
% 1.52/0.62  fof(f49,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.52/0.62    inference(cnf_transformation,[],[f8])).
% 1.52/0.62  fof(f8,axiom,(
% 1.52/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.52/0.62  fof(f270,plain,(
% 1.52/0.62    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.52/0.62    inference(superposition,[],[f73,f76])).
% 1.52/0.62  fof(f73,plain,(
% 1.52/0.62    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))),
% 1.52/0.62    inference(definition_unfolding,[],[f40,f71,f72])).
% 1.52/0.62  fof(f72,plain,(
% 1.52/0.62    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.52/0.62    inference(definition_unfolding,[],[f43,f70])).
% 1.52/0.62  fof(f43,plain,(
% 1.52/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f12])).
% 1.52/0.62  fof(f12,axiom,(
% 1.52/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.52/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.52/0.62  fof(f40,plain,(
% 1.52/0.62    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.52/0.62    inference(cnf_transformation,[],[f27])).
% 1.52/0.62  % SZS output end Proof for theBenchmark
% 1.52/0.62  % (28138)------------------------------
% 1.52/0.62  % (28138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.62  % (28138)Termination reason: Refutation
% 1.52/0.62  
% 1.52/0.62  % (28138)Memory used [KB]: 6396
% 1.52/0.62  % (28138)Time elapsed: 0.200 s
% 1.52/0.62  % (28138)------------------------------
% 1.52/0.62  % (28138)------------------------------
% 1.52/0.63  % (28110)Success in time 0.252 s
%------------------------------------------------------------------------------
