%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t72_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:31 EDT 2019

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 114 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 252 expanded)
%              Number of equality atoms :   54 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1521,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1520,f38])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f32])).

fof(f32,plain,
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

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t72_xboole_1.p',t72_xboole_1)).

fof(f1520,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1492,f1147])).

fof(f1147,plain,(
    k3_xboole_0(sK1,sK2) = sK1 ),
    inference(subsumption_resolution,[],[f1097,f61])).

fof(f61,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t72_xboole_1.p',symmetry_r1_xboole_0)).

fof(f1097,plain,
    ( k3_xboole_0(sK1,sK2) = sK1
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f558,f340])).

fof(f340,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X3,X2)) = X2 ),
    inference(backward_demodulation,[],[f337,f117])).

fof(f117,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f102,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t72_xboole_1.p',commutativity_k2_xboole_0)).

fof(f102,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X2) = k3_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f53,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t72_xboole_1.p',idempotence_k3_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t72_xboole_1.p',t23_xboole_1)).

fof(f337,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6 ),
    inference(subsumption_resolution,[],[f315,f45])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t72_xboole_1.p',t7_xboole_1)).

fof(f315,plain,(
    ! [X6,X7] :
      ( k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6
      | ~ r1_tarski(X6,k2_xboole_0(X6,X7)) ) ),
    inference(superposition,[],[f96,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t72_xboole_1.p',t28_xboole_1)).

fof(f96,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f53,f43])).

fof(f558,plain,(
    ! [X19] :
      ( k3_xboole_0(X19,sK2) = k3_xboole_0(X19,k2_xboole_0(sK0,sK1))
      | ~ r1_xboole_0(X19,sK3) ) ),
    inference(superposition,[],[f118,f35])).

fof(f35,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f118,plain,(
    ! [X6,X4,X5] :
      ( k3_xboole_0(X4,X6) = k3_xboole_0(X4,k2_xboole_0(X6,X5))
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(forward_demodulation,[],[f103,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t72_xboole_1.p',t1_boole)).

fof(f103,plain,(
    ! [X6,X4,X5] :
      ( k2_xboole_0(k3_xboole_0(X4,X6),k1_xboole_0) = k3_xboole_0(X4,k2_xboole_0(X6,X5))
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f53,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t72_xboole_1.p',d7_xboole_0)).

fof(f1492,plain,(
    k3_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[],[f549,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t72_xboole_1.p',commutativity_k3_xboole_0)).

fof(f549,plain,(
    k3_xboole_0(sK2,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f525,f36])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f525,plain,
    ( k3_xboole_0(sK2,sK1) = sK2
    | ~ r1_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f115,f344])).

fof(f344,plain,(
    k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = sK2 ),
    inference(backward_demodulation,[],[f337,f314])).

fof(f314,plain,(
    k2_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f96,f35])).

fof(f115,plain,(
    ! [X6,X4,X5] :
      ( k3_xboole_0(X4,X6) = k3_xboole_0(X4,k2_xboole_0(X5,X6))
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(forward_demodulation,[],[f97,f62])).

fof(f62,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f46,f40])).

fof(f97,plain,(
    ! [X6,X4,X5] :
      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X4,X6)) = k3_xboole_0(X4,k2_xboole_0(X5,X6))
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f53,f50])).
%------------------------------------------------------------------------------
