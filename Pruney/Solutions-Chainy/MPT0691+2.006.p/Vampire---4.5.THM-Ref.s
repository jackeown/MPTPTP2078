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
% DateTime   : Thu Dec  3 12:53:45 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 229 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  150 ( 514 expanded)
%              Number of equality atoms :   54 ( 132 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f770,plain,(
    $false ),
    inference(subsumption_resolution,[],[f767,f34])).

fof(f34,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f767,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f733,f759])).

fof(f759,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f751,f293])).

fof(f293,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0) ),
    inference(resolution,[],[f133,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X1),X1) ) ),
    inference(resolution,[],[f39,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f751,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f404,f530])).

fof(f530,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f512,f184])).

fof(f184,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f120,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f120,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f55,f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f47,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f512,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f509,f36])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f509,plain,(
    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f54,f501])).

fof(f501,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f470,f33])).

fof(f33,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f470,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f281,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f281,plain,(
    ! [X10,X9] :
      ( r1_tarski(k4_xboole_0(X10,X9),k1_xboole_0)
      | ~ r1_tarski(X10,X9) ) ),
    inference(superposition,[],[f93,f168])).

fof(f168,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(subsumption_resolution,[],[f163,f63])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f163,plain,(
    ! [X2] :
      ( k2_xboole_0(k1_xboole_0,X2) = X2
      | ~ r1_tarski(X2,k2_xboole_0(k1_xboole_0,X2)) ) ),
    inference(resolution,[],[f161,f50])).

fof(f161,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[],[f90,f36])).

fof(f90,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(k2_xboole_0(X6,X7),X6),X7) ),
    inference(resolution,[],[f52,f57])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_xboole_0(X1,X0))
      | r1_tarski(k4_xboole_0(X2,X0),X1) ) ),
    inference(superposition,[],[f52,f43])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f404,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f70,f32])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f733,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))) ),
    inference(superposition,[],[f704,f530])).

fof(f704,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X1)))) ),
    inference(superposition,[],[f228,f386])).

fof(f386,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f68,f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f37,f46])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f228,plain,(
    ! [X2,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(sK1,X2)) ),
    inference(superposition,[],[f59,f153])).

fof(f153,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f56,f32])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f51,f44])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f53,f42])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:35:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (14549)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (14566)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (14558)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (14550)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (14556)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (14558)Refutation not found, incomplete strategy% (14558)------------------------------
% 0.21/0.52  % (14558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14555)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (14558)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14558)Memory used [KB]: 10746
% 0.21/0.53  % (14558)Time elapsed: 0.119 s
% 0.21/0.53  % (14558)------------------------------
% 0.21/0.53  % (14558)------------------------------
% 1.27/0.53  % (14548)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.54  % (14573)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.27/0.54  % (14572)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.54  % (14551)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.54  % (14559)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.27/0.54  % (14571)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.55  % (14563)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.55  % (14576)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.50/0.55  % (14576)Refutation not found, incomplete strategy% (14576)------------------------------
% 1.50/0.55  % (14576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (14576)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (14576)Memory used [KB]: 10746
% 1.50/0.55  % (14576)Time elapsed: 0.148 s
% 1.50/0.55  % (14576)------------------------------
% 1.50/0.55  % (14576)------------------------------
% 1.50/0.56  % (14562)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.50/0.56  % (14561)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.56  % (14567)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.50/0.56  % (14569)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.56  % (14560)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.50/0.57  % (14557)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.57  % (14565)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.57  % (14553)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.57  % (14577)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.50/0.57  % (14577)Refutation not found, incomplete strategy% (14577)------------------------------
% 1.50/0.57  % (14577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (14577)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (14577)Memory used [KB]: 1663
% 1.50/0.57  % (14577)Time elapsed: 0.003 s
% 1.50/0.57  % (14577)------------------------------
% 1.50/0.57  % (14577)------------------------------
% 1.50/0.57  % (14552)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.50/0.58  % (14554)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.58  % (14575)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.58  % (14570)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.50/0.58  % (14574)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.50/0.59  % (14564)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.59  % (14564)Refutation not found, incomplete strategy% (14564)------------------------------
% 1.50/0.59  % (14564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.59  % (14564)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.59  
% 1.50/0.59  % (14564)Memory used [KB]: 10618
% 1.50/0.59  % (14564)Time elapsed: 0.180 s
% 1.50/0.59  % (14564)------------------------------
% 1.50/0.59  % (14564)------------------------------
% 1.50/0.59  % (14568)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.63  % (14554)Refutation found. Thanks to Tanya!
% 1.50/0.63  % SZS status Theorem for theBenchmark
% 1.50/0.63  % SZS output start Proof for theBenchmark
% 1.50/0.63  fof(f770,plain,(
% 1.50/0.63    $false),
% 1.50/0.63    inference(subsumption_resolution,[],[f767,f34])).
% 1.50/0.63  fof(f34,plain,(
% 1.50/0.63    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.50/0.63    inference(cnf_transformation,[],[f29])).
% 1.50/0.63  fof(f29,plain,(
% 1.50/0.63    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.50/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f28])).
% 1.50/0.63  fof(f28,plain,(
% 1.50/0.63    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.50/0.63    introduced(choice_axiom,[])).
% 1.50/0.63  fof(f20,plain,(
% 1.50/0.63    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.50/0.63    inference(flattening,[],[f19])).
% 1.50/0.63  fof(f19,plain,(
% 1.50/0.63    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.50/0.63    inference(ennf_transformation,[],[f18])).
% 1.50/0.63  fof(f18,negated_conjecture,(
% 1.50/0.63    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.50/0.63    inference(negated_conjecture,[],[f17])).
% 1.50/0.63  fof(f17,conjecture,(
% 1.50/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.50/0.63  fof(f767,plain,(
% 1.50/0.63    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.50/0.63    inference(backward_demodulation,[],[f733,f759])).
% 1.50/0.63  fof(f759,plain,(
% 1.50/0.63    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 1.50/0.63    inference(forward_demodulation,[],[f751,f293])).
% 1.50/0.63  fof(f293,plain,(
% 1.50/0.63    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)) )),
% 1.50/0.63    inference(resolution,[],[f133,f32])).
% 1.50/0.63  fof(f32,plain,(
% 1.50/0.63    v1_relat_1(sK1)),
% 1.50/0.63    inference(cnf_transformation,[],[f29])).
% 1.50/0.63  fof(f133,plain,(
% 1.50/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X1),X1)) )),
% 1.50/0.63    inference(resolution,[],[f39,f57])).
% 1.50/0.63  fof(f57,plain,(
% 1.50/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.63    inference(equality_resolution,[],[f49])).
% 1.50/0.63  fof(f49,plain,(
% 1.50/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.63    inference(cnf_transformation,[],[f31])).
% 1.50/0.63  fof(f31,plain,(
% 1.50/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.63    inference(flattening,[],[f30])).
% 1.50/0.63  fof(f30,plain,(
% 1.50/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.63    inference(nnf_transformation,[],[f2])).
% 1.50/0.63  fof(f2,axiom,(
% 1.50/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.63  fof(f39,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f23])).
% 1.50/0.63  fof(f23,plain,(
% 1.50/0.63    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.50/0.63    inference(ennf_transformation,[],[f13])).
% 1.50/0.63  fof(f13,axiom,(
% 1.50/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 1.50/0.63  fof(f751,plain,(
% 1.50/0.63    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 1.50/0.63    inference(superposition,[],[f404,f530])).
% 1.50/0.63  fof(f530,plain,(
% 1.50/0.63    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.50/0.63    inference(superposition,[],[f512,f184])).
% 1.50/0.63  fof(f184,plain,(
% 1.50/0.63    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 1.50/0.63    inference(superposition,[],[f120,f42])).
% 1.50/0.63  fof(f42,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f9])).
% 1.50/0.63  fof(f9,axiom,(
% 1.50/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.50/0.63  fof(f120,plain,(
% 1.50/0.63    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 1.50/0.63    inference(resolution,[],[f55,f32])).
% 1.50/0.63  fof(f55,plain,(
% 1.50/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 1.50/0.63    inference(definition_unfolding,[],[f47,f44])).
% 1.50/0.63  fof(f44,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.50/0.63    inference(cnf_transformation,[],[f10])).
% 1.50/0.63  fof(f10,axiom,(
% 1.50/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.50/0.63  fof(f47,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f25])).
% 1.50/0.63  fof(f25,plain,(
% 1.50/0.63    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.50/0.63    inference(ennf_transformation,[],[f15])).
% 1.50/0.63  fof(f15,axiom,(
% 1.50/0.63    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.50/0.63  fof(f512,plain,(
% 1.50/0.63    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 1.50/0.63    inference(forward_demodulation,[],[f509,f36])).
% 1.50/0.63  fof(f36,plain,(
% 1.50/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.50/0.63    inference(cnf_transformation,[],[f5])).
% 1.50/0.63  fof(f5,axiom,(
% 1.50/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.50/0.63  fof(f509,plain,(
% 1.50/0.63    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.50/0.63    inference(superposition,[],[f54,f501])).
% 1.50/0.63  fof(f501,plain,(
% 1.50/0.63    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 1.50/0.63    inference(resolution,[],[f470,f33])).
% 1.50/0.63  fof(f33,plain,(
% 1.50/0.63    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.50/0.63    inference(cnf_transformation,[],[f29])).
% 1.50/0.63  fof(f470,plain,(
% 1.50/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.50/0.63    inference(resolution,[],[f281,f71])).
% 1.50/0.63  fof(f71,plain,(
% 1.50/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.50/0.63    inference(resolution,[],[f50,f35])).
% 1.50/0.63  fof(f35,plain,(
% 1.50/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f4])).
% 1.50/0.63  fof(f4,axiom,(
% 1.50/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.50/0.63  fof(f50,plain,(
% 1.50/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f31])).
% 1.50/0.63  fof(f281,plain,(
% 1.50/0.63    ( ! [X10,X9] : (r1_tarski(k4_xboole_0(X10,X9),k1_xboole_0) | ~r1_tarski(X10,X9)) )),
% 1.50/0.63    inference(superposition,[],[f93,f168])).
% 1.50/0.63  fof(f168,plain,(
% 1.50/0.63    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) )),
% 1.50/0.63    inference(subsumption_resolution,[],[f163,f63])).
% 1.50/0.63  fof(f63,plain,(
% 1.50/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.50/0.63    inference(superposition,[],[f40,f43])).
% 1.50/0.63  fof(f43,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f1])).
% 1.50/0.63  fof(f1,axiom,(
% 1.50/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.50/0.63  fof(f40,plain,(
% 1.50/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.50/0.63    inference(cnf_transformation,[],[f8])).
% 1.50/0.63  fof(f8,axiom,(
% 1.50/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.50/0.63  fof(f163,plain,(
% 1.50/0.63    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2 | ~r1_tarski(X2,k2_xboole_0(k1_xboole_0,X2))) )),
% 1.50/0.63    inference(resolution,[],[f161,f50])).
% 1.50/0.63  fof(f161,plain,(
% 1.50/0.63    ( ! [X0] : (r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0)) )),
% 1.50/0.63    inference(superposition,[],[f90,f36])).
% 1.50/0.63  fof(f90,plain,(
% 1.50/0.63    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(k2_xboole_0(X6,X7),X6),X7)) )),
% 1.50/0.63    inference(resolution,[],[f52,f57])).
% 1.50/0.63  fof(f52,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.50/0.63    inference(cnf_transformation,[],[f27])).
% 1.50/0.63  fof(f27,plain,(
% 1.50/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.50/0.63    inference(ennf_transformation,[],[f6])).
% 1.50/0.63  fof(f6,axiom,(
% 1.50/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.50/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.50/0.63  fof(f93,plain,(
% 1.50/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_xboole_0(X1,X0)) | r1_tarski(k4_xboole_0(X2,X0),X1)) )),
% 1.50/0.63    inference(superposition,[],[f52,f43])).
% 1.50/0.63  fof(f54,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.50/0.63    inference(definition_unfolding,[],[f45,f44])).
% 1.50/0.63  fof(f45,plain,(
% 1.50/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.50/0.63    inference(cnf_transformation,[],[f7])).
% 2.06/0.64  fof(f7,axiom,(
% 2.06/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.06/0.64  fof(f404,plain,(
% 2.06/0.64    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.06/0.64    inference(resolution,[],[f70,f32])).
% 2.06/0.64  fof(f70,plain,(
% 2.06/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1)))) )),
% 2.06/0.64    inference(resolution,[],[f38,f46])).
% 2.06/0.64  fof(f46,plain,(
% 2.06/0.64    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f24])).
% 2.06/0.64  fof(f24,plain,(
% 2.06/0.64    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.06/0.64    inference(ennf_transformation,[],[f11])).
% 2.06/0.64  fof(f11,axiom,(
% 2.06/0.64    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.06/0.64  fof(f38,plain,(
% 2.06/0.64    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f22])).
% 2.06/0.64  fof(f22,plain,(
% 2.06/0.64    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.06/0.64    inference(ennf_transformation,[],[f12])).
% 2.06/0.64  fof(f12,axiom,(
% 2.06/0.64    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 2.06/0.64  fof(f733,plain,(
% 2.06/0.64    r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0))))),
% 2.06/0.64    inference(superposition,[],[f704,f530])).
% 2.06/0.64  fof(f704,plain,(
% 2.06/0.64    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X1))))) )),
% 2.06/0.64    inference(superposition,[],[f228,f386])).
% 2.06/0.64  fof(f386,plain,(
% 2.06/0.64    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.06/0.64    inference(resolution,[],[f68,f32])).
% 2.06/0.64  fof(f68,plain,(
% 2.06/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1)))) )),
% 2.06/0.64    inference(resolution,[],[f37,f46])).
% 2.06/0.64  fof(f37,plain,(
% 2.06/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 2.06/0.64    inference(cnf_transformation,[],[f21])).
% 2.06/0.64  fof(f21,plain,(
% 2.06/0.64    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.06/0.64    inference(ennf_transformation,[],[f14])).
% 2.06/0.64  fof(f14,axiom,(
% 2.06/0.64    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.06/0.64  fof(f228,plain,(
% 2.06/0.64    ( ! [X2,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X1),X2),k10_relat_1(sK1,X2))) )),
% 2.06/0.64    inference(superposition,[],[f59,f153])).
% 2.06/0.64  fof(f153,plain,(
% 2.06/0.64    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))) )),
% 2.06/0.64    inference(resolution,[],[f56,f32])).
% 2.06/0.64  fof(f56,plain,(
% 2.06/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 2.06/0.64    inference(definition_unfolding,[],[f51,f44])).
% 2.06/0.64  fof(f51,plain,(
% 2.06/0.64    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f26])).
% 2.06/0.64  fof(f26,plain,(
% 2.06/0.64    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.06/0.64    inference(ennf_transformation,[],[f16])).
% 2.06/0.64  fof(f16,axiom,(
% 2.06/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 2.06/0.64  fof(f59,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 2.06/0.64    inference(superposition,[],[f53,f42])).
% 2.06/0.64  fof(f53,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 2.06/0.64    inference(definition_unfolding,[],[f41,f44])).
% 2.06/0.64  fof(f41,plain,(
% 2.06/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.06/0.64    inference(cnf_transformation,[],[f3])).
% 2.06/0.64  fof(f3,axiom,(
% 2.06/0.64    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.06/0.64  % SZS output end Proof for theBenchmark
% 2.06/0.64  % (14554)------------------------------
% 2.06/0.64  % (14554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.64  % (14554)Termination reason: Refutation
% 2.06/0.64  
% 2.06/0.64  % (14554)Memory used [KB]: 11257
% 2.06/0.64  % (14554)Time elapsed: 0.221 s
% 2.06/0.64  % (14554)------------------------------
% 2.06/0.64  % (14554)------------------------------
% 2.06/0.64  % (14547)Success in time 0.277 s
%------------------------------------------------------------------------------
