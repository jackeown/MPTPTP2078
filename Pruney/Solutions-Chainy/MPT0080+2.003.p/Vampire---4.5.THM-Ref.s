%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:59 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 225 expanded)
%              Number of leaves         :   17 (  71 expanded)
%              Depth                    :   26
%              Number of atoms          :  149 ( 332 expanded)
%              Number of equality atoms :   56 ( 180 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1663,plain,(
    $false ),
    inference(resolution,[],[f1652,f33])).

fof(f33,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f1652,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f56,f1626])).

fof(f1626,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1625,f85])).

fof(f85,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f82,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f82,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f79,f35])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f79,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f41,f35])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1625,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f1620,f38])).

fof(f1620,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f40,f1598])).

fof(f1598,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f1548,f253])).

fof(f253,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f102,f250])).

fof(f250,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f95,f246])).

fof(f246,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f244,f35])).

fof(f244,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f48,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f95,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f41,f85])).

fof(f102,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f78,f95])).

fof(f78,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f41,f60])).

fof(f60,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f44,f31])).

fof(f31,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1548,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2)) ),
    inference(superposition,[],[f1279,f38])).

fof(f1279,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f50,f1223])).

fof(f1223,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f1222,f85])).

fof(f1222,plain,(
    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) ),
    inference(forward_demodulation,[],[f1212,f38])).

fof(f1212,plain,(
    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[],[f1192,f50])).

fof(f1192,plain,(
    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1191,f598])).

fof(f598,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f593,f40])).

fof(f593,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f246,f50])).

fof(f1191,plain,(
    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f1146,f50])).

fof(f1146,plain,(
    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) ),
    inference(superposition,[],[f600,f211])).

fof(f211,plain,(
    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f210,f85])).

fof(f210,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f209,f38])).

fof(f209,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f40,f175])).

fof(f175,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f172,f82])).

fof(f172,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X0) = X0 ),
    inference(resolution,[],[f170,f44])).

fof(f170,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X0) ),
    inference(resolution,[],[f167,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f167,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f600,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X6 ),
    inference(forward_demodulation,[],[f599,f35])).

fof(f599,plain,(
    ! [X6,X5] : k4_xboole_0(X6,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f381,f598])).

fof(f381,plain,(
    ! [X6,X5] : k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(X5,X6))) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f51,f41])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f39,f39])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f36,f38])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:29:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (28273)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.48  % (28257)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.50  % (28266)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (28266)Refutation not found, incomplete strategy% (28266)------------------------------
% 0.22/0.50  % (28266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28266)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28266)Memory used [KB]: 10618
% 0.22/0.50  % (28266)Time elapsed: 0.095 s
% 0.22/0.50  % (28266)------------------------------
% 0.22/0.50  % (28266)------------------------------
% 0.22/0.50  % (28267)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (28252)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (28253)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (28254)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (28253)Refutation not found, incomplete strategy% (28253)------------------------------
% 0.22/0.52  % (28253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28253)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28253)Memory used [KB]: 10618
% 0.22/0.52  % (28253)Time elapsed: 0.106 s
% 0.22/0.52  % (28253)------------------------------
% 0.22/0.52  % (28253)------------------------------
% 0.22/0.52  % (28248)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (28245)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (28258)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (28262)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (28249)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (28250)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (28247)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (28269)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (28268)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (28271)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (28244)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (28244)Refutation not found, incomplete strategy% (28244)------------------------------
% 0.22/0.54  % (28244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28244)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28244)Memory used [KB]: 1663
% 0.22/0.54  % (28244)Time elapsed: 0.125 s
% 0.22/0.54  % (28244)------------------------------
% 0.22/0.54  % (28244)------------------------------
% 0.22/0.54  % (28254)Refutation not found, incomplete strategy% (28254)------------------------------
% 0.22/0.54  % (28254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28254)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28254)Memory used [KB]: 10618
% 0.22/0.54  % (28254)Time elapsed: 0.127 s
% 0.22/0.54  % (28254)------------------------------
% 0.22/0.54  % (28254)------------------------------
% 0.22/0.54  % (28255)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (28270)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (28255)Refutation not found, incomplete strategy% (28255)------------------------------
% 0.22/0.54  % (28255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28255)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28255)Memory used [KB]: 10618
% 0.22/0.54  % (28255)Time elapsed: 0.141 s
% 0.22/0.54  % (28255)------------------------------
% 0.22/0.54  % (28255)------------------------------
% 0.22/0.54  % (28265)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (28263)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (28272)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (28246)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (28251)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (28264)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (28261)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (28261)Refutation not found, incomplete strategy% (28261)------------------------------
% 0.22/0.55  % (28261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28261)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28261)Memory used [KB]: 10618
% 0.22/0.55  % (28261)Time elapsed: 0.149 s
% 0.22/0.55  % (28261)------------------------------
% 0.22/0.55  % (28261)------------------------------
% 0.22/0.55  % (28259)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (28256)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (28260)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.79/0.59  % (28274)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.65  % (28256)Refutation found. Thanks to Tanya!
% 2.11/0.65  % SZS status Theorem for theBenchmark
% 2.11/0.65  % SZS output start Proof for theBenchmark
% 2.11/0.65  fof(f1663,plain,(
% 2.11/0.65    $false),
% 2.11/0.65    inference(resolution,[],[f1652,f33])).
% 2.11/0.65  fof(f33,plain,(
% 2.11/0.65    ~r1_tarski(sK0,sK1)),
% 2.11/0.65    inference(cnf_transformation,[],[f23])).
% 2.11/0.65  fof(f23,plain,(
% 2.11/0.65    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).
% 2.11/0.65  fof(f22,plain,(
% 2.11/0.65    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f18,plain,(
% 2.11/0.65    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.11/0.65    inference(flattening,[],[f17])).
% 2.11/0.65  fof(f17,plain,(
% 2.11/0.65    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.11/0.65    inference(ennf_transformation,[],[f15])).
% 2.11/0.65  fof(f15,negated_conjecture,(
% 2.11/0.65    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.11/0.65    inference(negated_conjecture,[],[f14])).
% 2.11/0.65  fof(f14,conjecture,(
% 2.11/0.65    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 2.11/0.65  fof(f1652,plain,(
% 2.11/0.65    r1_tarski(sK0,sK1)),
% 2.11/0.65    inference(superposition,[],[f56,f1626])).
% 2.11/0.65  fof(f1626,plain,(
% 2.11/0.65    sK1 = k2_xboole_0(sK1,sK0)),
% 2.11/0.65    inference(forward_demodulation,[],[f1625,f85])).
% 2.11/0.65  fof(f85,plain,(
% 2.11/0.65    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.11/0.65    inference(superposition,[],[f82,f38])).
% 2.11/0.65  fof(f38,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f1])).
% 2.11/0.65  fof(f1,axiom,(
% 2.11/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.11/0.65  fof(f82,plain,(
% 2.11/0.65    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.11/0.65    inference(forward_demodulation,[],[f79,f35])).
% 2.11/0.65  fof(f35,plain,(
% 2.11/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.11/0.65    inference(cnf_transformation,[],[f8])).
% 2.11/0.65  fof(f8,axiom,(
% 2.11/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.11/0.65  fof(f79,plain,(
% 2.11/0.65    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 2.11/0.65    inference(superposition,[],[f41,f35])).
% 2.11/0.65  fof(f41,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f9])).
% 2.11/0.65  fof(f9,axiom,(
% 2.11/0.65    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.11/0.65  fof(f1625,plain,(
% 2.11/0.65    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1)),
% 2.11/0.65    inference(forward_demodulation,[],[f1620,f38])).
% 2.11/0.65  fof(f1620,plain,(
% 2.11/0.65    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 2.11/0.65    inference(superposition,[],[f40,f1598])).
% 2.11/0.65  fof(f1598,plain,(
% 2.11/0.65    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 2.11/0.65    inference(superposition,[],[f1548,f253])).
% 2.11/0.65  fof(f253,plain,(
% 2.11/0.65    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.11/0.65    inference(backward_demodulation,[],[f102,f250])).
% 2.11/0.65  fof(f250,plain,(
% 2.11/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.11/0.65    inference(backward_demodulation,[],[f95,f246])).
% 2.11/0.65  fof(f246,plain,(
% 2.11/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.11/0.65    inference(forward_demodulation,[],[f244,f35])).
% 2.11/0.65  fof(f244,plain,(
% 2.11/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.11/0.65    inference(resolution,[],[f55,f34])).
% 2.11/0.65  fof(f34,plain,(
% 2.11/0.65    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f12])).
% 2.11/0.65  fof(f12,axiom,(
% 2.11/0.65    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.11/0.65  fof(f55,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.11/0.65    inference(definition_unfolding,[],[f48,f39])).
% 2.11/0.65  fof(f39,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f11])).
% 2.11/0.65  fof(f11,axiom,(
% 2.11/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.11/0.65  fof(f48,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f30])).
% 2.11/0.65  fof(f30,plain,(
% 2.11/0.65    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.11/0.65    inference(nnf_transformation,[],[f4])).
% 2.11/0.65  fof(f4,axiom,(
% 2.11/0.65    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.11/0.65  fof(f95,plain,(
% 2.11/0.65    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 2.11/0.65    inference(superposition,[],[f41,f85])).
% 2.11/0.65  fof(f102,plain,(
% 2.11/0.65    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))),
% 2.11/0.65    inference(backward_demodulation,[],[f78,f95])).
% 2.11/0.65  fof(f78,plain,(
% 2.11/0.65    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))),
% 2.11/0.65    inference(superposition,[],[f41,f60])).
% 2.11/0.65  fof(f60,plain,(
% 2.11/0.65    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.11/0.65    inference(resolution,[],[f44,f31])).
% 2.11/0.65  fof(f31,plain,(
% 2.11/0.65    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.11/0.65    inference(cnf_transformation,[],[f23])).
% 2.11/0.65  fof(f44,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.11/0.65    inference(cnf_transformation,[],[f20])).
% 2.11/0.65  fof(f20,plain,(
% 2.11/0.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.11/0.65    inference(ennf_transformation,[],[f6])).
% 2.11/0.65  fof(f6,axiom,(
% 2.11/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.11/0.65  fof(f1548,plain,(
% 2.11/0.65    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))) )),
% 2.11/0.65    inference(superposition,[],[f1279,f38])).
% 2.11/0.65  fof(f1279,plain,(
% 2.11/0.65    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))) )),
% 2.11/0.65    inference(superposition,[],[f50,f1223])).
% 2.11/0.65  fof(f1223,plain,(
% 2.11/0.65    sK0 = k4_xboole_0(sK0,sK2)),
% 2.11/0.65    inference(forward_demodulation,[],[f1222,f85])).
% 2.11/0.65  fof(f1222,plain,(
% 2.11/0.65    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2))),
% 2.11/0.65    inference(forward_demodulation,[],[f1212,f38])).
% 2.11/0.65  fof(f1212,plain,(
% 2.11/0.65    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k1_xboole_0))),
% 2.11/0.65    inference(superposition,[],[f1192,f50])).
% 2.11/0.65  fof(f1192,plain,(
% 2.11/0.65    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 2.11/0.65    inference(forward_demodulation,[],[f1191,f598])).
% 2.11/0.65  fof(f598,plain,(
% 2.11/0.65    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.11/0.65    inference(forward_demodulation,[],[f593,f40])).
% 2.11/0.65  fof(f593,plain,(
% 2.11/0.65    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 2.11/0.65    inference(superposition,[],[f246,f50])).
% 2.11/0.65  fof(f1191,plain,(
% 2.11/0.65    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)))),
% 2.11/0.65    inference(forward_demodulation,[],[f1146,f50])).
% 2.11/0.65  fof(f1146,plain,(
% 2.11/0.65    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0))),
% 2.11/0.65    inference(superposition,[],[f600,f211])).
% 2.11/0.65  fof(f211,plain,(
% 2.11/0.65    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 2.11/0.65    inference(forward_demodulation,[],[f210,f85])).
% 2.11/0.65  fof(f210,plain,(
% 2.11/0.65    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 2.11/0.65    inference(forward_demodulation,[],[f209,f38])).
% 2.11/0.65  fof(f209,plain,(
% 2.11/0.65    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 2.11/0.65    inference(superposition,[],[f40,f175])).
% 2.11/0.65  fof(f175,plain,(
% 2.11/0.65    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.11/0.65    inference(superposition,[],[f172,f82])).
% 2.11/0.65  fof(f172,plain,(
% 2.11/0.65    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X0) = X0) )),
% 2.11/0.65    inference(resolution,[],[f170,f44])).
% 2.11/0.65  fof(f170,plain,(
% 2.11/0.65    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X0)) )),
% 2.11/0.65    inference(resolution,[],[f167,f46])).
% 2.11/0.65  fof(f46,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f29])).
% 2.11/0.65  fof(f29,plain,(
% 2.11/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 2.11/0.65  fof(f28,plain,(
% 2.11/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f27,plain,(
% 2.11/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.65    inference(rectify,[],[f26])).
% 2.11/0.65  fof(f26,plain,(
% 2.11/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.65    inference(nnf_transformation,[],[f21])).
% 2.11/0.65  fof(f21,plain,(
% 2.11/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.11/0.65    inference(ennf_transformation,[],[f3])).
% 2.11/0.65  fof(f3,axiom,(
% 2.11/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.11/0.65  fof(f167,plain,(
% 2.11/0.65    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) )),
% 2.11/0.65    inference(resolution,[],[f52,f32])).
% 2.11/0.65  fof(f32,plain,(
% 2.11/0.65    r1_xboole_0(sK0,sK2)),
% 2.11/0.65    inference(cnf_transformation,[],[f23])).
% 2.11/0.65  fof(f52,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.11/0.65    inference(definition_unfolding,[],[f43,f39])).
% 2.11/0.65  fof(f43,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f25])).
% 2.11/0.65  fof(f25,plain,(
% 2.11/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f24])).
% 2.11/0.65  fof(f24,plain,(
% 2.11/0.65    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f19,plain,(
% 2.11/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.11/0.65    inference(ennf_transformation,[],[f16])).
% 2.11/0.65  fof(f16,plain,(
% 2.11/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.11/0.65    inference(rectify,[],[f5])).
% 2.11/0.65  fof(f5,axiom,(
% 2.11/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.11/0.65  fof(f600,plain,(
% 2.11/0.65    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X6) )),
% 2.11/0.65    inference(forward_demodulation,[],[f599,f35])).
% 2.11/0.65  fof(f599,plain,(
% 2.11/0.65    ( ! [X6,X5] : (k4_xboole_0(X6,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 2.11/0.65    inference(backward_demodulation,[],[f381,f598])).
% 2.11/0.65  fof(f381,plain,(
% 2.11/0.65    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(X5,X6))) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 2.11/0.65    inference(superposition,[],[f51,f41])).
% 2.11/0.65  fof(f51,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.11/0.65    inference(definition_unfolding,[],[f37,f39,f39])).
% 2.11/0.65  fof(f37,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f2])).
% 2.11/0.65  fof(f2,axiom,(
% 2.11/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.11/0.65  fof(f50,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f10])).
% 2.11/0.65  fof(f10,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.11/0.65  fof(f40,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f7])).
% 2.11/0.65  fof(f7,axiom,(
% 2.11/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.11/0.65  fof(f56,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 2.11/0.65    inference(superposition,[],[f36,f38])).
% 2.11/0.65  fof(f36,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f13])).
% 2.11/0.65  fof(f13,axiom,(
% 2.11/0.65    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.11/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.11/0.65  % SZS output end Proof for theBenchmark
% 2.11/0.65  % (28256)------------------------------
% 2.11/0.65  % (28256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.65  % (28256)Termination reason: Refutation
% 2.11/0.65  
% 2.11/0.65  % (28256)Memory used [KB]: 7164
% 2.11/0.65  % (28256)Time elapsed: 0.222 s
% 2.11/0.65  % (28256)------------------------------
% 2.11/0.65  % (28256)------------------------------
% 2.11/0.67  % (28243)Success in time 0.306 s
%------------------------------------------------------------------------------
