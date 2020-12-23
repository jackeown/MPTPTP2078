%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:51 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  140 (2230 expanded)
%              Number of leaves         :   16 ( 706 expanded)
%              Depth                    :   38
%              Number of atoms          :  182 (4368 expanded)
%              Number of equality atoms :  133 (2239 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1359,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1358])).

fof(f1358,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f33,f1217])).

fof(f1217,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1216,f63])).

fof(f63,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f61,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f61,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f59,f34])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f59,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f41,f34])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1216,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f1207,f1212])).

fof(f1212,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1211,f929])).

fof(f929,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f69,f918])).

fof(f918,plain,(
    ! [X10] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10) ),
    inference(superposition,[],[f516,f63])).

fof(f516,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    inference(backward_demodulation,[],[f287,f515])).

fof(f515,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2 ),
    inference(forward_demodulation,[],[f486,f398])).

fof(f398,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f39,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f486,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2 ),
    inference(superposition,[],[f52,f50])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f287,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k2_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f276,f38])).

fof(f276,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f42,f50])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f69,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f41,f63])).

fof(f1211,plain,(
    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1204,f670])).

fof(f670,plain,(
    ! [X4] : k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k4_xboole_0(sK0,X4) ),
    inference(forward_demodulation,[],[f656,f464])).

fof(f464,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f48,f417])).

fof(f417,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f402,f34])).

fof(f402,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f51,f93])).

fof(f93,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f91,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f89,f50])).

fof(f89,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f53,f31])).

fof(f31,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f656,plain,(
    ! [X4] : k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK2,X4)) ),
    inference(superposition,[],[f464,f42])).

fof(f1204,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f50,f1184])).

fof(f1184,plain,(
    sK1 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f1183,f738])).

fof(f738,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f723,f429])).

fof(f429,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f403,f34])).

fof(f403,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f51,f96])).

fof(f96,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f92,f35])).

fof(f92,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f90,f50])).

fof(f90,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) ),
    inference(resolution,[],[f53,f32])).

fof(f32,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f723,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f466,f685])).

fof(f685,plain,(
    sK3 = k2_xboole_0(sK3,sK0) ),
    inference(forward_demodulation,[],[f684,f63])).

fof(f684,plain,(
    k2_xboole_0(sK3,sK0) = k2_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f681,f38])).

fof(f681,plain,(
    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f42,f664])).

fof(f664,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f663,f350])).

fof(f350,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f342,f96])).

fof(f342,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f119,f103])).

fof(f103,plain,(
    k4_xboole_0(sK1,sK3) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(forward_demodulation,[],[f102,f63])).

fof(f102,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f101,f38])).

fof(f101,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[],[f42,f96])).

fof(f119,plain,(
    ! [X15] : k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X15)) = k4_xboole_0(k1_xboole_0,X15) ),
    inference(superposition,[],[f48,f96])).

fof(f663,plain,(
    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f650,f421])).

fof(f421,plain,(
    ! [X14] : k4_xboole_0(k1_xboole_0,X14) = k4_xboole_0(sK0,k2_xboole_0(sK0,X14)) ),
    inference(backward_demodulation,[],[f118,f417])).

fof(f118,plain,(
    ! [X14] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X14)) = k4_xboole_0(k1_xboole_0,X14) ),
    inference(superposition,[],[f48,f93])).

fof(f650,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f464,f30])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f466,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f48,f429])).

fof(f1183,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1153,f57])).

fof(f57,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f41,f38])).

fof(f1153,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f57,f765])).

fof(f765,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f302,f757])).

fof(f757,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f756,f38])).

fof(f756,plain,(
    sK2 = k2_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f755,f63])).

fof(f755,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f752,f38])).

fof(f752,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f42,f740])).

fof(f740,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f739,f158])).

fof(f158,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f150,f93])).

fof(f150,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f118,f100])).

fof(f100,plain,(
    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f99,f63])).

fof(f99,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f98,f38])).

fof(f98,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f42,f93])).

fof(f739,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f724,f438])).

fof(f438,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK1)) ),
    inference(backward_demodulation,[],[f344,f429])).

fof(f344,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,k4_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f119,f38])).

fof(f724,plain,(
    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f466,f536])).

fof(f536,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f518,f42])).

fof(f518,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f490,f358])).

fof(f358,plain,(
    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f355,f34])).

fof(f355,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f281,f350])).

fof(f281,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f265,f206])).

fof(f206,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f88,f205])).

fof(f205,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f48,f158])).

fof(f88,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f87,f69])).

fof(f87,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f41,f83])).

fof(f83,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f82,f30])).

fof(f82,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f81,f38])).

fof(f81,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f74,f42])).

fof(f74,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f42,f56])).

fof(f56,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f41,f30])).

fof(f265,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f50,f56])).

fof(f490,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f52,f56])).

fof(f302,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f301,f80])).

fof(f80,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,X2) ),
    inference(forward_demodulation,[],[f73,f42])).

fof(f73,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f42,f41])).

fof(f301,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f300,f80])).

fof(f300,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f299,f181])).

fof(f181,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f49,f38])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f299,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    inference(forward_demodulation,[],[f291,f181])).

fof(f291,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f197,f83])).

fof(f197,plain,(
    ! [X24] : k2_xboole_0(sK2,k2_xboole_0(sK3,X24)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X24)) ),
    inference(forward_demodulation,[],[f177,f49])).

fof(f177,plain,(
    ! [X24] : k2_xboole_0(sK2,k2_xboole_0(sK3,X24)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X24) ),
    inference(superposition,[],[f49,f30])).

fof(f1207,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK1),sK1) ),
    inference(superposition,[],[f52,f1184])).

fof(f33,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (31557)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (31570)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (31560)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (31575)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (31568)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (31562)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (31575)Refutation not found, incomplete strategy% (31575)------------------------------
% 0.20/0.54  % (31575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31575)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31575)Memory used [KB]: 10618
% 0.20/0.54  % (31575)Time elapsed: 0.101 s
% 0.20/0.54  % (31575)------------------------------
% 0.20/0.54  % (31575)------------------------------
% 1.43/0.55  % (31558)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.43/0.55  % (31588)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.57/0.57  % (31561)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.57/0.57  % (31570)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.57  % SZS output start Proof for theBenchmark
% 1.57/0.57  fof(f1359,plain,(
% 1.57/0.57    $false),
% 1.57/0.57    inference(trivial_inequality_removal,[],[f1358])).
% 1.57/0.57  fof(f1358,plain,(
% 1.57/0.57    sK1 != sK1),
% 1.57/0.57    inference(superposition,[],[f33,f1217])).
% 1.57/0.57  fof(f1217,plain,(
% 1.57/0.57    sK1 = sK2),
% 1.57/0.57    inference(forward_demodulation,[],[f1216,f63])).
% 1.57/0.57  fof(f63,plain,(
% 1.57/0.57    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.57/0.57    inference(superposition,[],[f61,f38])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.57/0.57  fof(f61,plain,(
% 1.57/0.57    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.57/0.57    inference(forward_demodulation,[],[f59,f34])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.57/0.57  fof(f59,plain,(
% 1.57/0.57    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 1.57/0.57    inference(superposition,[],[f41,f34])).
% 1.57/0.57  fof(f41,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.57/0.57  fof(f1216,plain,(
% 1.57/0.57    sK2 = k2_xboole_0(k1_xboole_0,sK1)),
% 1.57/0.57    inference(forward_demodulation,[],[f1207,f1212])).
% 1.57/0.57  fof(f1212,plain,(
% 1.57/0.57    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.57/0.57    inference(forward_demodulation,[],[f1211,f929])).
% 1.57/0.57  fof(f929,plain,(
% 1.57/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.57/0.57    inference(backward_demodulation,[],[f69,f918])).
% 1.57/0.57  fof(f918,plain,(
% 1.57/0.57    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10)) )),
% 1.57/0.57    inference(superposition,[],[f516,f63])).
% 1.57/0.57  fof(f516,plain,(
% 1.57/0.57    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) )),
% 1.57/0.57    inference(backward_demodulation,[],[f287,f515])).
% 1.57/0.57  fof(f515,plain,(
% 1.57/0.57    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2) )),
% 1.57/0.57    inference(forward_demodulation,[],[f486,f398])).
% 1.57/0.57  fof(f398,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.57/0.57    inference(superposition,[],[f51,f50])).
% 1.57/0.57  fof(f50,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.57/0.57    inference(definition_unfolding,[],[f37,f39,f39])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f12])).
% 1.57/0.57  fof(f12,axiom,(
% 1.57/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.57/0.57  fof(f51,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.57/0.57    inference(definition_unfolding,[],[f40,f39])).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,axiom,(
% 1.57/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.57/0.57  fof(f486,plain,(
% 1.57/0.57    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2) )),
% 1.57/0.57    inference(superposition,[],[f52,f50])).
% 1.57/0.57  fof(f52,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.57/0.57    inference(definition_unfolding,[],[f43,f39])).
% 1.57/0.57  fof(f43,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,axiom,(
% 1.57/0.57    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.57/0.57  fof(f287,plain,(
% 1.57/0.57    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k2_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 1.57/0.57    inference(forward_demodulation,[],[f276,f38])).
% 1.57/0.57  fof(f276,plain,(
% 1.57/0.57    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3)))) )),
% 1.57/0.57    inference(superposition,[],[f42,f50])).
% 1.57/0.57  fof(f42,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.57/0.57  fof(f69,plain,(
% 1.57/0.57    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.57/0.57    inference(superposition,[],[f41,f63])).
% 1.57/0.57  fof(f1211,plain,(
% 1.57/0.57    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK2,sK1)),
% 1.57/0.57    inference(forward_demodulation,[],[f1204,f670])).
% 1.57/0.57  fof(f670,plain,(
% 1.57/0.57    ( ! [X4] : (k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k4_xboole_0(sK0,X4)) )),
% 1.57/0.57    inference(forward_demodulation,[],[f656,f464])).
% 1.57/0.57  fof(f464,plain,(
% 1.57/0.57    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))) )),
% 1.57/0.57    inference(superposition,[],[f48,f417])).
% 1.57/0.57  fof(f417,plain,(
% 1.57/0.57    sK0 = k4_xboole_0(sK0,sK2)),
% 1.57/0.57    inference(forward_demodulation,[],[f402,f34])).
% 1.57/0.57  fof(f402,plain,(
% 1.57/0.57    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.57/0.57    inference(superposition,[],[f51,f93])).
% 1.57/0.57  fof(f93,plain,(
% 1.57/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.57/0.57    inference(resolution,[],[f91,f35])).
% 1.57/0.57  fof(f35,plain,(
% 1.57/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.57/0.57    inference(ennf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.57/0.57  fof(f91,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) )),
% 1.57/0.57    inference(forward_demodulation,[],[f89,f50])).
% 1.57/0.57  fof(f89,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) )),
% 1.57/0.57    inference(resolution,[],[f53,f31])).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    r1_xboole_0(sK2,sK0)),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f23])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f20,plain,(
% 1.57/0.57    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.57/0.57    inference(flattening,[],[f19])).
% 1.57/0.57  fof(f19,plain,(
% 1.57/0.57    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.57/0.57    inference(ennf_transformation,[],[f16])).
% 1.57/0.57  fof(f16,negated_conjecture,(
% 1.57/0.57    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.57/0.57    inference(negated_conjecture,[],[f15])).
% 1.57/0.57  fof(f15,conjecture,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.57/0.57  fof(f53,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.57/0.57    inference(definition_unfolding,[],[f45,f39])).
% 1.57/0.57  fof(f45,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f18])).
% 1.57/0.57  fof(f18,plain,(
% 1.57/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.57    inference(rectify,[],[f4])).
% 1.57/0.57  fof(f4,axiom,(
% 1.57/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f10])).
% 1.57/0.57  fof(f10,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.57/0.57  fof(f656,plain,(
% 1.57/0.57    ( ! [X4] : (k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK2,X4))) )),
% 1.57/0.57    inference(superposition,[],[f464,f42])).
% 1.57/0.57  fof(f1204,plain,(
% 1.57/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,sK1)),
% 1.57/0.57    inference(superposition,[],[f50,f1184])).
% 1.57/0.57  fof(f1184,plain,(
% 1.57/0.57    sK1 = k4_xboole_0(sK2,sK0)),
% 1.57/0.57    inference(forward_demodulation,[],[f1183,f738])).
% 1.57/0.57  fof(f738,plain,(
% 1.57/0.57    sK1 = k4_xboole_0(sK1,sK0)),
% 1.57/0.57    inference(forward_demodulation,[],[f723,f429])).
% 1.57/0.57  fof(f429,plain,(
% 1.57/0.57    sK1 = k4_xboole_0(sK1,sK3)),
% 1.57/0.57    inference(forward_demodulation,[],[f403,f34])).
% 1.57/0.57  fof(f403,plain,(
% 1.57/0.57    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.57/0.57    inference(superposition,[],[f51,f96])).
% 1.57/0.57  fof(f96,plain,(
% 1.57/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.57/0.57    inference(resolution,[],[f92,f35])).
% 1.57/0.57  fof(f92,plain,(
% 1.57/0.57    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))) )),
% 1.57/0.57    inference(forward_demodulation,[],[f90,f50])).
% 1.57/0.57  fof(f90,plain,(
% 1.57/0.57    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) )),
% 1.57/0.57    inference(resolution,[],[f53,f32])).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    r1_xboole_0(sK3,sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f723,plain,(
% 1.57/0.57    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK0)),
% 1.57/0.57    inference(superposition,[],[f466,f685])).
% 1.57/0.57  fof(f685,plain,(
% 1.57/0.57    sK3 = k2_xboole_0(sK3,sK0)),
% 1.57/0.57    inference(forward_demodulation,[],[f684,f63])).
% 1.57/0.57  fof(f684,plain,(
% 1.57/0.57    k2_xboole_0(sK3,sK0) = k2_xboole_0(k1_xboole_0,sK3)),
% 1.57/0.57    inference(forward_demodulation,[],[f681,f38])).
% 1.57/0.57  fof(f681,plain,(
% 1.57/0.57    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0)),
% 1.57/0.57    inference(superposition,[],[f42,f664])).
% 1.57/0.57  fof(f664,plain,(
% 1.57/0.57    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 1.57/0.57    inference(forward_demodulation,[],[f663,f350])).
% 1.57/0.57  fof(f350,plain,(
% 1.57/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 1.57/0.57    inference(forward_demodulation,[],[f342,f96])).
% 1.57/0.57  fof(f342,plain,(
% 1.57/0.57    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(k1_xboole_0,sK1)),
% 1.57/0.57    inference(superposition,[],[f119,f103])).
% 1.57/0.57  fof(f103,plain,(
% 1.57/0.57    k4_xboole_0(sK1,sK3) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 1.57/0.57    inference(forward_demodulation,[],[f102,f63])).
% 1.57/0.57  fof(f102,plain,(
% 1.57/0.57    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 1.57/0.57    inference(forward_demodulation,[],[f101,f38])).
% 1.57/0.57  fof(f101,plain,(
% 1.57/0.57    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)),
% 1.57/0.57    inference(superposition,[],[f42,f96])).
% 1.57/0.57  fof(f119,plain,(
% 1.57/0.57    ( ! [X15] : (k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X15)) = k4_xboole_0(k1_xboole_0,X15)) )),
% 1.57/0.57    inference(superposition,[],[f48,f96])).
% 1.57/0.57  fof(f663,plain,(
% 1.57/0.57    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK0,sK3)),
% 1.57/0.57    inference(forward_demodulation,[],[f650,f421])).
% 1.57/0.57  fof(f421,plain,(
% 1.57/0.57    ( ! [X14] : (k4_xboole_0(k1_xboole_0,X14) = k4_xboole_0(sK0,k2_xboole_0(sK0,X14))) )),
% 1.57/0.57    inference(backward_demodulation,[],[f118,f417])).
% 1.57/0.57  fof(f118,plain,(
% 1.57/0.57    ( ! [X14] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X14)) = k4_xboole_0(k1_xboole_0,X14)) )),
% 1.57/0.57    inference(superposition,[],[f48,f93])).
% 1.57/0.57  fof(f650,plain,(
% 1.57/0.57    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3)),
% 1.57/0.57    inference(superposition,[],[f464,f30])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f466,plain,(
% 1.57/0.57    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0))) )),
% 1.57/0.57    inference(superposition,[],[f48,f429])).
% 1.57/0.57  fof(f1183,plain,(
% 1.57/0.57    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0)),
% 1.57/0.57    inference(forward_demodulation,[],[f1153,f57])).
% 1.57/0.57  fof(f57,plain,(
% 1.57/0.57    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 1.57/0.57    inference(superposition,[],[f41,f38])).
% 1.57/0.57  fof(f1153,plain,(
% 1.57/0.57    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)),
% 1.57/0.57    inference(superposition,[],[f57,f765])).
% 1.57/0.57  fof(f765,plain,(
% 1.57/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)),
% 1.57/0.57    inference(backward_demodulation,[],[f302,f757])).
% 1.57/0.57  fof(f757,plain,(
% 1.57/0.57    sK2 = k2_xboole_0(sK1,sK2)),
% 1.57/0.57    inference(superposition,[],[f756,f38])).
% 1.57/0.57  fof(f756,plain,(
% 1.57/0.57    sK2 = k2_xboole_0(sK2,sK1)),
% 1.57/0.57    inference(forward_demodulation,[],[f755,f63])).
% 1.57/0.57  fof(f755,plain,(
% 1.57/0.57    k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2)),
% 1.57/0.57    inference(forward_demodulation,[],[f752,f38])).
% 1.57/0.57  fof(f752,plain,(
% 1.57/0.57    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 1.57/0.57    inference(superposition,[],[f42,f740])).
% 1.57/0.57  fof(f740,plain,(
% 1.57/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.57/0.57    inference(forward_demodulation,[],[f739,f158])).
% 1.57/0.57  fof(f158,plain,(
% 1.57/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 1.57/0.57    inference(forward_demodulation,[],[f150,f93])).
% 1.57/0.57  fof(f150,plain,(
% 1.57/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k1_xboole_0,sK0)),
% 1.57/0.57    inference(superposition,[],[f118,f100])).
% 1.57/0.57  fof(f100,plain,(
% 1.57/0.57    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 1.57/0.57    inference(forward_demodulation,[],[f99,f63])).
% 1.57/0.57  fof(f99,plain,(
% 1.57/0.57    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 1.57/0.57    inference(forward_demodulation,[],[f98,f38])).
% 1.57/0.57  fof(f98,plain,(
% 1.57/0.57    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 1.57/0.57    inference(superposition,[],[f42,f93])).
% 1.57/0.57  fof(f739,plain,(
% 1.57/0.57    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK1,sK2)),
% 1.57/0.57    inference(forward_demodulation,[],[f724,f438])).
% 1.57/0.57  fof(f438,plain,(
% 1.57/0.57    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK1))) )),
% 1.57/0.57    inference(backward_demodulation,[],[f344,f429])).
% 1.57/0.57  fof(f344,plain,(
% 1.57/0.57    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,k4_xboole_0(sK1,sK3)))) )),
% 1.57/0.57    inference(superposition,[],[f119,f38])).
% 1.57/0.57  fof(f724,plain,(
% 1.57/0.57    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2)),
% 1.57/0.57    inference(superposition,[],[f466,f536])).
% 1.57/0.57  fof(f536,plain,(
% 1.57/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 1.57/0.57    inference(superposition,[],[f518,f42])).
% 1.57/0.57  fof(f518,plain,(
% 1.57/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 1.57/0.57    inference(forward_demodulation,[],[f490,f358])).
% 1.57/0.57  fof(f358,plain,(
% 1.57/0.57    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3))),
% 1.57/0.57    inference(forward_demodulation,[],[f355,f34])).
% 1.57/0.57  fof(f355,plain,(
% 1.57/0.57    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k1_xboole_0)),
% 1.57/0.57    inference(backward_demodulation,[],[f281,f350])).
% 1.57/0.57  fof(f281,plain,(
% 1.57/0.57    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK1))),
% 1.57/0.57    inference(forward_demodulation,[],[f265,f206])).
% 1.57/0.57  fof(f206,plain,(
% 1.57/0.57    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK1)),
% 1.57/0.57    inference(backward_demodulation,[],[f88,f205])).
% 1.57/0.57  fof(f205,plain,(
% 1.57/0.57    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0))) )),
% 1.57/0.57    inference(superposition,[],[f48,f158])).
% 1.57/0.57  fof(f88,plain,(
% 1.57/0.57    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 1.57/0.57    inference(forward_demodulation,[],[f87,f69])).
% 1.57/0.57  fof(f87,plain,(
% 1.57/0.57    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.57/0.57    inference(superposition,[],[f41,f83])).
% 1.57/0.57  fof(f83,plain,(
% 1.57/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.57/0.57    inference(forward_demodulation,[],[f82,f30])).
% 1.57/0.57  fof(f82,plain,(
% 1.57/0.57    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.57/0.57    inference(forward_demodulation,[],[f81,f38])).
% 1.57/0.57  fof(f81,plain,(
% 1.57/0.57    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.57/0.57    inference(forward_demodulation,[],[f74,f42])).
% 1.57/0.57  fof(f74,plain,(
% 1.57/0.57    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 1.57/0.57    inference(superposition,[],[f42,f56])).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.57/0.57    inference(superposition,[],[f41,f30])).
% 1.57/0.57  fof(f265,plain,(
% 1.57/0.57    k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3))),
% 1.57/0.57    inference(superposition,[],[f50,f56])).
% 1.57/0.57  fof(f490,plain,(
% 1.57/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3))),
% 1.57/0.57    inference(superposition,[],[f52,f56])).
% 1.57/0.57  fof(f302,plain,(
% 1.57/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.57/0.57    inference(forward_demodulation,[],[f301,f80])).
% 1.57/0.57  fof(f80,plain,(
% 1.57/0.57    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,X2)) )),
% 1.57/0.57    inference(forward_demodulation,[],[f73,f42])).
% 1.57/0.57  fof(f73,plain,(
% 1.57/0.57    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 1.57/0.57    inference(superposition,[],[f42,f41])).
% 1.57/0.57  fof(f301,plain,(
% 1.57/0.57    k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 1.57/0.57    inference(forward_demodulation,[],[f300,f80])).
% 1.57/0.57  fof(f300,plain,(
% 1.57/0.57    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.57/0.57    inference(forward_demodulation,[],[f299,f181])).
% 1.57/0.57  fof(f181,plain,(
% 1.57/0.57    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 1.57/0.57    inference(superposition,[],[f49,f38])).
% 1.57/0.57  fof(f49,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f13])).
% 1.57/0.57  fof(f13,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.57/0.57  fof(f299,plain,(
% 1.57/0.57    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 1.57/0.57    inference(forward_demodulation,[],[f291,f181])).
% 1.57/0.57  fof(f291,plain,(
% 1.57/0.57    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.57/0.57    inference(superposition,[],[f197,f83])).
% 1.57/0.57  fof(f197,plain,(
% 1.57/0.57    ( ! [X24] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X24)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X24))) )),
% 1.57/0.57    inference(forward_demodulation,[],[f177,f49])).
% 1.57/0.57  fof(f177,plain,(
% 1.57/0.57    ( ! [X24] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X24)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X24)) )),
% 1.57/0.57    inference(superposition,[],[f49,f30])).
% 1.57/0.57  fof(f1207,plain,(
% 1.57/0.57    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK1),sK1)),
% 1.57/0.57    inference(superposition,[],[f52,f1184])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    sK1 != sK2),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (31570)------------------------------
% 1.57/0.57  % (31570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (31570)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (31570)Memory used [KB]: 6908
% 1.57/0.57  % (31570)Time elapsed: 0.116 s
% 1.57/0.57  % (31570)------------------------------
% 1.57/0.57  % (31570)------------------------------
% 1.57/0.57  % (31555)Success in time 0.214 s
%------------------------------------------------------------------------------
