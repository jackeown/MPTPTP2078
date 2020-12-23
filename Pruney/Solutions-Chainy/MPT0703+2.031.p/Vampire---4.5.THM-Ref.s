%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:22 EST 2020

% Result     : Theorem 3.85s
% Output     : Refutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 251 expanded)
%              Number of leaves         :   13 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  186 ( 827 expanded)
%              Number of equality atoms :   34 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3238,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f35,f2752,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f2752,plain,(
    ! [X21] : r1_tarski(k2_xboole_0(sK0,k4_xboole_0(sK1,X21)),sK1) ),
    inference(forward_demodulation,[],[f2720,f701])).

fof(f701,plain,(
    ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(subsumption_resolution,[],[f690,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f44,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f690,plain,(
    ! [X9] :
      ( k2_xboole_0(X9,k1_xboole_0) = X9
      | ~ r1_tarski(X9,k2_xboole_0(X9,k1_xboole_0)) ) ),
    inference(resolution,[],[f186,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f186,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,k1_xboole_0),X0) ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,X6)
      | r1_tarski(k2_xboole_0(X5,k1_xboole_0),X6) ) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f2720,plain,(
    ! [X21] : r1_tarski(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,k1_xboole_0),X21)),k2_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f226,f2447])).

fof(f2447,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f2434,f790])).

fof(f790,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f100,f781])).

fof(f781,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f554,f57])).

fof(f57,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f42,f36])).

fof(f554,plain,(
    ! [X1] : r1_tarski(k10_relat_1(sK2,k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f535,f526])).

fof(f526,plain,(
    ! [X22] : k1_xboole_0 = k4_xboole_0(X22,X22) ),
    inference(resolution,[],[f67,f57])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f43,f53])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f535,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(X0,X0)),X1) ),
    inference(superposition,[],[f67,f83])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f82,f31])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f51,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f46,f38])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f100,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) ),
    inference(resolution,[],[f81,f36])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f80,f31])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f39,f32])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f2434,plain,(
    k9_relat_1(sK2,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f101,f2223])).

fof(f2223,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f2071,f57])).

fof(f2071,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK1)),X2) ),
    inference(forward_demodulation,[],[f2058,f83])).

fof(f2058,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X2) ),
    inference(resolution,[],[f983,f43])).

fof(f983,plain,(
    ! [X67] : r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X67)) ),
    inference(resolution,[],[f62,f33])).

fof(f33,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(X2,k2_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f47,f53])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f101,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(sK0,X0))) ),
    inference(resolution,[],[f81,f86])).

fof(f86,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k2_relat_1(sK2)) ),
    inference(resolution,[],[f66,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f66,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,sK0)
      | r1_tarski(X11,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f47,f34])).

fof(f34,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f226,plain,(
    ! [X10,X8,X9] : r1_tarski(k2_xboole_0(X8,k4_xboole_0(k2_xboole_0(X9,k4_xboole_0(X8,X9)),X10)),k2_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(resolution,[],[f77,f72])).

fof(f72,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(resolution,[],[f45,f49])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f77,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(k2_xboole_0(X7,k4_xboole_0(X8,X9)),X8) ) ),
    inference(resolution,[],[f48,f37])).

fof(f35,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:06:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (9370)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.19/0.51  % (9376)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.52  % (9384)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.53  % (9378)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.53  % (9387)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.32/0.54  % (9373)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.54  % (9391)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.54  % (9396)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.54  % (9372)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.54  % (9383)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.32/0.54  % (9394)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.54  % (9398)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.55  % (9386)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.32/0.55  % (9397)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.55  % (9377)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.55  % (9375)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.32/0.55  % (9379)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.55  % (9392)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.55  % (9374)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.55  % (9399)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.56  % (9389)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.32/0.56  % (9381)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.57  % (9382)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.32/0.57  % (9371)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.57  % (9371)Refutation not found, incomplete strategy% (9371)------------------------------
% 1.32/0.57  % (9371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (9371)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (9371)Memory used [KB]: 1663
% 1.32/0.57  % (9371)Time elapsed: 0.150 s
% 1.32/0.57  % (9371)------------------------------
% 1.32/0.57  % (9371)------------------------------
% 1.32/0.57  % (9388)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.57  % (9390)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.58  % (9385)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.58  % (9395)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.58  % (9380)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.58  % (9393)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.62  % (9370)Refutation not found, incomplete strategy% (9370)------------------------------
% 1.32/0.62  % (9370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.63  % (9370)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.63  
% 2.01/0.63  % (9370)Memory used [KB]: 1663
% 2.01/0.63  % (9370)Time elapsed: 0.196 s
% 2.01/0.63  % (9370)------------------------------
% 2.01/0.63  % (9370)------------------------------
% 2.01/0.68  % (9373)Refutation not found, incomplete strategy% (9373)------------------------------
% 2.01/0.68  % (9373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  % (9373)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.68  
% 2.01/0.68  % (9373)Memory used [KB]: 6140
% 2.01/0.68  % (9373)Time elapsed: 0.266 s
% 2.01/0.68  % (9373)------------------------------
% 2.01/0.68  % (9373)------------------------------
% 2.58/0.71  % (9400)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.58/0.74  % (9401)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.09/0.83  % (9372)Time limit reached!
% 3.09/0.83  % (9372)------------------------------
% 3.09/0.83  % (9372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.83  % (9402)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.09/0.84  % (9394)Time limit reached!
% 3.09/0.84  % (9394)------------------------------
% 3.09/0.84  % (9394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.84  % (9394)Termination reason: Time limit
% 3.09/0.84  % (9394)Termination phase: Saturation
% 3.09/0.84  
% 3.09/0.84  % (9394)Memory used [KB]: 12153
% 3.09/0.84  % (9394)Time elapsed: 0.400 s
% 3.09/0.84  % (9394)------------------------------
% 3.09/0.84  % (9394)------------------------------
% 3.09/0.85  % (9372)Termination reason: Time limit
% 3.09/0.85  % (9372)Termination phase: Saturation
% 3.09/0.85  
% 3.09/0.85  % (9372)Memory used [KB]: 6908
% 3.09/0.85  % (9372)Time elapsed: 0.400 s
% 3.09/0.85  % (9372)------------------------------
% 3.09/0.85  % (9372)------------------------------
% 3.09/0.85  % (9402)Refutation not found, incomplete strategy% (9402)------------------------------
% 3.09/0.85  % (9402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.85  % (9402)Termination reason: Refutation not found, incomplete strategy
% 3.09/0.85  
% 3.09/0.85  % (9402)Memory used [KB]: 6140
% 3.09/0.85  % (9402)Time elapsed: 0.119 s
% 3.09/0.85  % (9402)------------------------------
% 3.09/0.85  % (9402)------------------------------
% 3.85/0.88  % (9377)Refutation found. Thanks to Tanya!
% 3.85/0.88  % SZS status Theorem for theBenchmark
% 3.85/0.88  % SZS output start Proof for theBenchmark
% 3.85/0.88  fof(f3238,plain,(
% 3.85/0.88    $false),
% 3.85/0.88    inference(unit_resulting_resolution,[],[f35,f2752,f44])).
% 3.85/0.88  fof(f44,plain,(
% 3.85/0.88    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 3.85/0.88    inference(cnf_transformation,[],[f19])).
% 3.85/0.88  fof(f19,plain,(
% 3.85/0.88    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.85/0.88    inference(ennf_transformation,[],[f2])).
% 3.85/0.88  fof(f2,axiom,(
% 3.85/0.88    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 3.85/0.88  fof(f2752,plain,(
% 3.85/0.88    ( ! [X21] : (r1_tarski(k2_xboole_0(sK0,k4_xboole_0(sK1,X21)),sK1)) )),
% 3.85/0.88    inference(forward_demodulation,[],[f2720,f701])).
% 3.85/0.88  fof(f701,plain,(
% 3.85/0.88    ( ! [X9] : (k2_xboole_0(X9,k1_xboole_0) = X9) )),
% 3.85/0.88    inference(subsumption_resolution,[],[f690,f53])).
% 3.85/0.88  fof(f53,plain,(
% 3.85/0.88    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.85/0.88    inference(resolution,[],[f44,f49])).
% 3.85/0.88  fof(f49,plain,(
% 3.85/0.88    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.85/0.88    inference(equality_resolution,[],[f41])).
% 3.85/0.88  fof(f41,plain,(
% 3.85/0.88    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.85/0.88    inference(cnf_transformation,[],[f30])).
% 3.85/0.88  fof(f30,plain,(
% 3.85/0.88    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.85/0.88    inference(flattening,[],[f29])).
% 3.85/0.88  fof(f29,plain,(
% 3.85/0.88    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.85/0.88    inference(nnf_transformation,[],[f1])).
% 3.85/0.88  fof(f1,axiom,(
% 3.85/0.88    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.85/0.88  fof(f690,plain,(
% 3.85/0.88    ( ! [X9] : (k2_xboole_0(X9,k1_xboole_0) = X9 | ~r1_tarski(X9,k2_xboole_0(X9,k1_xboole_0))) )),
% 3.85/0.88    inference(resolution,[],[f186,f42])).
% 3.85/0.88  fof(f42,plain,(
% 3.85/0.88    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.85/0.88    inference(cnf_transformation,[],[f30])).
% 3.85/0.88  fof(f186,plain,(
% 3.85/0.88    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,k1_xboole_0),X0)) )),
% 3.85/0.88    inference(resolution,[],[f76,f49])).
% 3.85/0.88  fof(f76,plain,(
% 3.85/0.88    ( ! [X6,X5] : (~r1_tarski(X5,X6) | r1_tarski(k2_xboole_0(X5,k1_xboole_0),X6)) )),
% 3.85/0.88    inference(resolution,[],[f48,f36])).
% 3.85/0.88  fof(f36,plain,(
% 3.85/0.88    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.85/0.88    inference(cnf_transformation,[],[f4])).
% 3.85/0.88  fof(f4,axiom,(
% 3.85/0.88    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.85/0.88  fof(f48,plain,(
% 3.85/0.88    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.85/0.88    inference(cnf_transformation,[],[f26])).
% 3.85/0.88  fof(f26,plain,(
% 3.85/0.88    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.85/0.88    inference(flattening,[],[f25])).
% 3.85/0.88  fof(f25,plain,(
% 3.85/0.88    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.85/0.88    inference(ennf_transformation,[],[f8])).
% 3.85/0.88  fof(f8,axiom,(
% 3.85/0.88    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 3.85/0.88  fof(f2720,plain,(
% 3.85/0.88    ( ! [X21] : (r1_tarski(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,k1_xboole_0),X21)),k2_xboole_0(sK1,k1_xboole_0))) )),
% 3.85/0.88    inference(superposition,[],[f226,f2447])).
% 3.85/0.88  fof(f2447,plain,(
% 3.85/0.88    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 3.85/0.88    inference(forward_demodulation,[],[f2434,f790])).
% 3.85/0.88  fof(f790,plain,(
% 3.85/0.88    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 3.85/0.88    inference(backward_demodulation,[],[f100,f781])).
% 3.85/0.88  fof(f781,plain,(
% 3.85/0.88    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 3.85/0.88    inference(resolution,[],[f554,f57])).
% 3.85/0.88  fof(f57,plain,(
% 3.85/0.88    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 3.85/0.88    inference(resolution,[],[f42,f36])).
% 3.85/0.88  fof(f554,plain,(
% 3.85/0.88    ( ! [X1] : (r1_tarski(k10_relat_1(sK2,k1_xboole_0),X1)) )),
% 3.85/0.88    inference(forward_demodulation,[],[f535,f526])).
% 3.85/0.88  fof(f526,plain,(
% 3.85/0.88    ( ! [X22] : (k1_xboole_0 = k4_xboole_0(X22,X22)) )),
% 3.85/0.88    inference(resolution,[],[f67,f57])).
% 3.85/0.88  fof(f67,plain,(
% 3.85/0.88    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 3.85/0.88    inference(resolution,[],[f43,f53])).
% 3.85/0.88  fof(f43,plain,(
% 3.85/0.88    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.85/0.88    inference(cnf_transformation,[],[f18])).
% 3.85/0.88  fof(f18,plain,(
% 3.85/0.88    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.85/0.88    inference(ennf_transformation,[],[f6])).
% 3.85/0.88  fof(f6,axiom,(
% 3.85/0.88    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.85/0.88  fof(f535,plain,(
% 3.85/0.88    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(X0,X0)),X1)) )),
% 3.85/0.88    inference(superposition,[],[f67,f83])).
% 3.85/0.88  fof(f83,plain,(
% 3.85/0.88    ( ! [X0,X1] : (k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))) )),
% 3.85/0.88    inference(subsumption_resolution,[],[f82,f31])).
% 3.85/0.88  fof(f31,plain,(
% 3.85/0.88    v1_relat_1(sK2)),
% 3.85/0.88    inference(cnf_transformation,[],[f28])).
% 3.85/0.88  fof(f28,plain,(
% 3.85/0.88    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.85/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27])).
% 3.85/0.88  fof(f27,plain,(
% 3.85/0.88    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.85/0.88    introduced(choice_axiom,[])).
% 3.85/0.88  fof(f15,plain,(
% 3.85/0.88    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.85/0.88    inference(flattening,[],[f14])).
% 3.85/0.88  fof(f14,plain,(
% 3.85/0.88    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.85/0.88    inference(ennf_transformation,[],[f13])).
% 3.85/0.88  fof(f13,negated_conjecture,(
% 3.85/0.88    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.85/0.88    inference(negated_conjecture,[],[f12])).
% 3.85/0.88  fof(f12,conjecture,(
% 3.85/0.88    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 3.85/0.88  fof(f82,plain,(
% 3.85/0.88    ( ! [X0,X1] : (k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1)) | ~v1_relat_1(sK2)) )),
% 3.85/0.88    inference(resolution,[],[f52,f32])).
% 3.85/0.88  fof(f32,plain,(
% 3.85/0.88    v1_funct_1(sK2)),
% 3.85/0.88    inference(cnf_transformation,[],[f28])).
% 3.85/0.88  fof(f52,plain,(
% 3.85/0.88    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.85/0.88    inference(forward_demodulation,[],[f51,f38])).
% 3.85/0.88  fof(f38,plain,(
% 3.85/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.85/0.88    inference(cnf_transformation,[],[f9])).
% 3.85/0.88  fof(f9,axiom,(
% 3.85/0.88    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.85/0.88  fof(f51,plain,(
% 3.85/0.88    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.85/0.88    inference(forward_demodulation,[],[f46,f38])).
% 3.85/0.88  fof(f46,plain,(
% 3.85/0.88    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.85/0.88    inference(cnf_transformation,[],[f22])).
% 3.85/0.88  fof(f22,plain,(
% 3.85/0.88    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.85/0.88    inference(flattening,[],[f21])).
% 3.85/0.88  fof(f21,plain,(
% 3.85/0.88    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.85/0.88    inference(ennf_transformation,[],[f10])).
% 3.85/0.88  fof(f10,axiom,(
% 3.85/0.88    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 3.85/0.88  fof(f100,plain,(
% 3.85/0.88    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))),
% 3.85/0.88    inference(resolution,[],[f81,f36])).
% 3.85/0.88  fof(f81,plain,(
% 3.85/0.88    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 3.85/0.88    inference(subsumption_resolution,[],[f80,f31])).
% 3.85/0.88  fof(f80,plain,(
% 3.85/0.88    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 3.85/0.88    inference(resolution,[],[f39,f32])).
% 3.85/0.88  fof(f39,plain,(
% 3.85/0.88    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 3.85/0.88    inference(cnf_transformation,[],[f17])).
% 3.85/0.88  fof(f17,plain,(
% 3.85/0.88    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.85/0.88    inference(flattening,[],[f16])).
% 3.85/0.88  fof(f16,plain,(
% 3.85/0.88    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.85/0.88    inference(ennf_transformation,[],[f11])).
% 3.85/0.88  fof(f11,axiom,(
% 3.85/0.88    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 3.85/0.88  fof(f2434,plain,(
% 3.85/0.88    k9_relat_1(sK2,k1_xboole_0) = k4_xboole_0(sK0,sK1)),
% 3.85/0.88    inference(superposition,[],[f101,f2223])).
% 3.85/0.88  fof(f2223,plain,(
% 3.85/0.88    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))),
% 3.85/0.88    inference(resolution,[],[f2071,f57])).
% 3.85/0.88  fof(f2071,plain,(
% 3.85/0.88    ( ! [X2] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK1)),X2)) )),
% 3.85/0.88    inference(forward_demodulation,[],[f2058,f83])).
% 3.85/0.88  fof(f2058,plain,(
% 3.85/0.88    ( ! [X2] : (r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X2)) )),
% 3.85/0.88    inference(resolution,[],[f983,f43])).
% 3.85/0.88  fof(f983,plain,(
% 3.85/0.88    ( ! [X67] : (r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X67))) )),
% 3.85/0.88    inference(resolution,[],[f62,f33])).
% 3.85/0.88  fof(f33,plain,(
% 3.85/0.88    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 3.85/0.88    inference(cnf_transformation,[],[f28])).
% 3.85/0.88  fof(f62,plain,(
% 3.85/0.88    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(X2,k2_xboole_0(X3,X4))) )),
% 3.85/0.88    inference(resolution,[],[f47,f53])).
% 3.85/0.88  fof(f47,plain,(
% 3.85/0.88    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.85/0.88    inference(cnf_transformation,[],[f24])).
% 3.85/0.88  fof(f24,plain,(
% 3.85/0.88    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.85/0.88    inference(flattening,[],[f23])).
% 3.85/0.88  fof(f23,plain,(
% 3.85/0.88    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.85/0.88    inference(ennf_transformation,[],[f3])).
% 3.85/0.88  fof(f3,axiom,(
% 3.85/0.88    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.85/0.88  fof(f101,plain,(
% 3.85/0.88    ( ! [X0] : (k4_xboole_0(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(sK0,X0)))) )),
% 3.85/0.88    inference(resolution,[],[f81,f86])).
% 3.85/0.88  fof(f86,plain,(
% 3.85/0.88    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k2_relat_1(sK2))) )),
% 3.85/0.88    inference(resolution,[],[f66,f37])).
% 3.85/0.88  fof(f37,plain,(
% 3.85/0.88    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.85/0.88    inference(cnf_transformation,[],[f5])).
% 3.85/0.88  fof(f5,axiom,(
% 3.85/0.88    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.85/0.88  fof(f66,plain,(
% 3.85/0.88    ( ! [X11] : (~r1_tarski(X11,sK0) | r1_tarski(X11,k2_relat_1(sK2))) )),
% 3.85/0.88    inference(resolution,[],[f47,f34])).
% 3.85/0.88  fof(f34,plain,(
% 3.85/0.88    r1_tarski(sK0,k2_relat_1(sK2))),
% 3.85/0.88    inference(cnf_transformation,[],[f28])).
% 3.85/0.88  fof(f226,plain,(
% 3.85/0.88    ( ! [X10,X8,X9] : (r1_tarski(k2_xboole_0(X8,k4_xboole_0(k2_xboole_0(X9,k4_xboole_0(X8,X9)),X10)),k2_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 3.85/0.88    inference(resolution,[],[f77,f72])).
% 3.85/0.88  fof(f72,plain,(
% 3.85/0.88    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3)))) )),
% 3.85/0.88    inference(resolution,[],[f45,f49])).
% 3.85/0.88  fof(f45,plain,(
% 3.85/0.88    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.85/0.88    inference(cnf_transformation,[],[f20])).
% 3.85/0.88  fof(f20,plain,(
% 3.85/0.88    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.85/0.88    inference(ennf_transformation,[],[f7])).
% 3.85/0.88  fof(f7,axiom,(
% 3.85/0.88    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.85/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.85/0.88  fof(f77,plain,(
% 3.85/0.88    ( ! [X8,X7,X9] : (~r1_tarski(X7,X8) | r1_tarski(k2_xboole_0(X7,k4_xboole_0(X8,X9)),X8)) )),
% 3.85/0.88    inference(resolution,[],[f48,f37])).
% 3.85/0.88  fof(f35,plain,(
% 3.85/0.88    ~r1_tarski(sK0,sK1)),
% 3.85/0.88    inference(cnf_transformation,[],[f28])).
% 3.85/0.88  % SZS output end Proof for theBenchmark
% 3.85/0.88  % (9377)------------------------------
% 3.85/0.88  % (9377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.88  % (9377)Termination reason: Refutation
% 3.85/0.88  
% 3.85/0.88  % (9377)Memory used [KB]: 5373
% 3.85/0.88  % (9377)Time elapsed: 0.445 s
% 3.85/0.88  % (9377)------------------------------
% 3.85/0.88  % (9377)------------------------------
% 3.85/0.88  % (9369)Success in time 0.513 s
%------------------------------------------------------------------------------
