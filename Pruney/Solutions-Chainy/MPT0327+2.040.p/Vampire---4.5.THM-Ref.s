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
% DateTime   : Thu Dec  3 12:42:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 897 expanded)
%              Number of leaves         :   17 ( 235 expanded)
%              Depth                    :   19
%              Number of atoms          :  123 (1772 expanded)
%              Number of equality atoms :   82 ( 927 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f583,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f575])).

fof(f575,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f550,f566])).

fof(f566,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f565,f309])).

fof(f309,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f297,f77])).

fof(f77,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f56,f66])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f64,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f297,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f235,f107])).

fof(f107,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f42,f85])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f83,f65])).

fof(f65,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f40,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,X1)) ),
    inference(resolution,[],[f54,f60])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f235,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(backward_demodulation,[],[f104,f225])).

fof(f225,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f211,f77])).

fof(f211,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f104,f85])).

fof(f104,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f42,f85])).

fof(f565,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f564,f531])).

fof(f531,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f529,f41])).

fof(f529,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f93,f29])).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f93,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | k2_enumset1(X6,X6,X6,X6) = k3_xboole_0(k2_enumset1(X6,X6,X6,X6),X7) ) ),
    inference(resolution,[],[f57,f40])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f564,plain,(
    k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f563,f41])).

fof(f563,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f557,f309])).

fof(f557,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f172,f531])).

fof(f172,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f53,f42])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f32,f31,f35,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f550,plain,(
    sK1 != k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f549,f531])).

fof(f549,plain,(
    sK1 != k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(backward_demodulation,[],[f468,f541])).

fof(f541,plain,(
    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f537,f319])).

fof(f319,plain,(
    ! [X2,X3] : k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2 ),
    inference(superposition,[],[f309,f235])).

fof(f537,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f148,f529])).

fof(f148,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f59,f41])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f31,f50])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f468,plain,(
    sK1 != k5_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(backward_demodulation,[],[f415,f153])).

fof(f153,plain,(
    ! [X2,X3] : k3_tarski(k2_enumset1(X2,X2,X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f59,f42])).

fof(f415,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(backward_demodulation,[],[f102,f327])).

fof(f327,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f235,f309])).

fof(f102,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(backward_demodulation,[],[f99,f42])).

fof(f99,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(forward_demodulation,[],[f52,f41])).

fof(f52,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f30,f31,f35,f51,f51])).

fof(f30,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (7490)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (7481)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (7506)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (7498)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (7492)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (7494)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (7483)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (7500)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (7503)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (7508)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (7484)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (7508)Refutation not found, incomplete strategy% (7508)------------------------------
% 0.21/0.54  % (7508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7508)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7508)Memory used [KB]: 6140
% 0.21/0.54  % (7508)Time elapsed: 0.128 s
% 0.21/0.54  % (7508)------------------------------
% 0.21/0.54  % (7508)------------------------------
% 0.21/0.54  % (7485)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (7486)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (7495)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (7491)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (7491)Refutation not found, incomplete strategy% (7491)------------------------------
% 0.21/0.54  % (7491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7491)Memory used [KB]: 10746
% 0.21/0.54  % (7491)Time elapsed: 0.134 s
% 0.21/0.54  % (7491)------------------------------
% 0.21/0.54  % (7491)------------------------------
% 0.21/0.55  % (7501)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (7505)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (7487)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (7509)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (7496)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (7497)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (7482)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (7510)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (7493)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (7510)Refutation not found, incomplete strategy% (7510)------------------------------
% 0.21/0.56  % (7510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7510)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7510)Memory used [KB]: 1663
% 0.21/0.56  % (7510)Time elapsed: 0.150 s
% 0.21/0.56  % (7510)------------------------------
% 0.21/0.56  % (7510)------------------------------
% 0.21/0.56  % (7507)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (7489)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (7509)Refutation not found, incomplete strategy% (7509)------------------------------
% 0.21/0.56  % (7509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7509)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7509)Memory used [KB]: 10746
% 0.21/0.56  % (7509)Time elapsed: 0.148 s
% 0.21/0.56  % (7509)------------------------------
% 0.21/0.56  % (7509)------------------------------
% 0.21/0.56  % (7493)Refutation not found, incomplete strategy% (7493)------------------------------
% 0.21/0.56  % (7493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7493)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7493)Memory used [KB]: 10618
% 0.21/0.56  % (7493)Time elapsed: 0.147 s
% 0.21/0.56  % (7493)------------------------------
% 0.21/0.56  % (7493)------------------------------
% 0.21/0.56  % (7488)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (7497)Refutation not found, incomplete strategy% (7497)------------------------------
% 0.21/0.56  % (7497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7497)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7497)Memory used [KB]: 10618
% 0.21/0.56  % (7497)Time elapsed: 0.156 s
% 0.21/0.56  % (7497)------------------------------
% 0.21/0.56  % (7497)------------------------------
% 0.21/0.56  % (7482)Refutation not found, incomplete strategy% (7482)------------------------------
% 0.21/0.56  % (7482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7482)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7482)Memory used [KB]: 1663
% 0.21/0.56  % (7482)Time elapsed: 0.148 s
% 0.21/0.56  % (7482)------------------------------
% 0.21/0.56  % (7482)------------------------------
% 0.21/0.56  % (7502)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.57  % (7504)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.57  % (7499)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.58  % (7499)Refutation not found, incomplete strategy% (7499)------------------------------
% 0.21/0.58  % (7499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (7499)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (7499)Memory used [KB]: 1663
% 0.21/0.58  % (7499)Time elapsed: 0.164 s
% 0.21/0.58  % (7499)------------------------------
% 0.21/0.58  % (7499)------------------------------
% 0.21/0.58  % (7486)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f583,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f575])).
% 0.21/0.58  fof(f575,plain,(
% 0.21/0.58    sK1 != sK1),
% 0.21/0.58    inference(superposition,[],[f550,f566])).
% 0.21/0.58  fof(f566,plain,(
% 0.21/0.58    sK1 = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.21/0.58    inference(forward_demodulation,[],[f565,f309])).
% 0.21/0.58  fof(f309,plain,(
% 0.21/0.58    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 0.21/0.58    inference(forward_demodulation,[],[f297,f77])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(backward_demodulation,[],[f56,f66])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.58    inference(superposition,[],[f64,f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(resolution,[],[f40,f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f36,f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.58  fof(f297,plain,(
% 0.21/0.58    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 0.21/0.58    inference(superposition,[],[f235,f107])).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 0.21/0.58    inference(superposition,[],[f42,f85])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f83,f65])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 0.21/0.58    inference(resolution,[],[f40,f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.58    inference(flattening,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.58    inference(nnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,X1))) )),
% 0.21/0.58    inference(resolution,[],[f54,f60])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f34,f35])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.58    inference(nnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.58  fof(f235,plain,(
% 0.21/0.58    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 0.21/0.58    inference(backward_demodulation,[],[f104,f225])).
% 0.21/0.58  fof(f225,plain,(
% 0.21/0.58    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.58    inference(forward_demodulation,[],[f211,f77])).
% 0.21/0.58  fof(f211,plain,(
% 0.21/0.58    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.58    inference(superposition,[],[f104,f85])).
% 0.21/0.58  fof(f104,plain,(
% 0.21/0.58    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 0.21/0.58    inference(superposition,[],[f42,f85])).
% 0.21/0.58  fof(f565,plain,(
% 0.21/0.58    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.21/0.58    inference(forward_demodulation,[],[f564,f531])).
% 0.21/0.58  fof(f531,plain,(
% 0.21/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.58    inference(superposition,[],[f529,f41])).
% 0.21/0.58  fof(f529,plain,(
% 0.21/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.58    inference(resolution,[],[f93,f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    r2_hidden(sK0,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.58    inference(negated_conjecture,[],[f19])).
% 0.21/0.58  fof(f19,conjecture,(
% 0.21/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    ( ! [X6,X7] : (~r2_hidden(X6,X7) | k2_enumset1(X6,X6,X6,X6) = k3_xboole_0(k2_enumset1(X6,X6,X6,X6),X7)) )),
% 0.21/0.58    inference(resolution,[],[f57,f40])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f38,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f39,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f47,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.58    inference(nnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.58  fof(f564,plain,(
% 0.21/0.58    k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.21/0.58    inference(forward_demodulation,[],[f563,f41])).
% 0.21/0.58  fof(f563,plain,(
% 0.21/0.58    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.21/0.58    inference(forward_demodulation,[],[f557,f309])).
% 0.21/0.58  fof(f557,plain,(
% 0.21/0.58    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.21/0.58    inference(superposition,[],[f172,f531])).
% 0.21/0.58  fof(f172,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f53,f42])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f32,f31,f35,f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.58  fof(f550,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.21/0.58    inference(backward_demodulation,[],[f549,f531])).
% 0.21/0.58  fof(f549,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(sK1,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))),
% 0.21/0.58    inference(backward_demodulation,[],[f468,f541])).
% 0.21/0.58  fof(f541,plain,(
% 0.21/0.58    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.58    inference(forward_demodulation,[],[f537,f319])).
% 0.21/0.58  fof(f319,plain,(
% 0.21/0.58    ( ! [X2,X3] : (k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2) )),
% 0.21/0.58    inference(superposition,[],[f309,f235])).
% 0.21/0.58  fof(f537,plain,(
% 0.21/0.58    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.58    inference(superposition,[],[f148,f529])).
% 0.21/0.58  fof(f148,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))) )),
% 0.21/0.58    inference(superposition,[],[f59,f41])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f48,f31,f50])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.58  fof(f468,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))),
% 0.21/0.58    inference(backward_demodulation,[],[f415,f153])).
% 0.21/0.58  fof(f153,plain,(
% 0.21/0.58    ( ! [X2,X3] : (k3_tarski(k2_enumset1(X2,X2,X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))) )),
% 0.21/0.58    inference(superposition,[],[f59,f42])).
% 0.21/0.58  fof(f415,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))),
% 0.21/0.58    inference(backward_demodulation,[],[f102,f327])).
% 0.21/0.58  fof(f327,plain,(
% 0.21/0.58    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 0.21/0.58    inference(superposition,[],[f235,f309])).
% 0.21/0.58  fof(f102,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))),
% 0.21/0.58    inference(backward_demodulation,[],[f99,f42])).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))),
% 0.21/0.58    inference(forward_demodulation,[],[f52,f41])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    sK1 != k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.58    inference(definition_unfolding,[],[f30,f31,f35,f51,f51])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.59    inference(cnf_transformation,[],[f24])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (7486)------------------------------
% 0.21/0.59  % (7486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (7486)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (7486)Memory used [KB]: 2046
% 0.21/0.59  % (7486)Time elapsed: 0.179 s
% 0.21/0.59  % (7486)------------------------------
% 0.21/0.59  % (7486)------------------------------
% 0.21/0.59  % (7480)Success in time 0.223 s
%------------------------------------------------------------------------------
