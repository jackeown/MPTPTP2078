%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:02 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 363 expanded)
%              Number of leaves         :   15 (  98 expanded)
%              Depth                    :   20
%              Number of atoms          :  181 ( 806 expanded)
%              Number of equality atoms :   29 ( 196 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1723,plain,(
    $false ),
    inference(resolution,[],[f1681,f1720])).

fof(f1720,plain,(
    ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(subsumption_resolution,[],[f1701,f954])).

fof(f954,plain,(
    ! [X16] : r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X16)))) ),
    inference(subsumption_resolution,[],[f945,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f945,plain,(
    ! [X16] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,X16))
      | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X16)))) ) ),
    inference(superposition,[],[f239,f758])).

fof(f758,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f723,f32])).

fof(f32,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f723,plain,(
    ! [X35,X34] :
      ( ~ r1_tarski(X34,X35)
      | k1_xboole_0 = k4_xboole_0(X34,X35) ) ),
    inference(resolution,[],[f712,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f712,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(global_subsumption,[],[f711])).

fof(f711,plain,(
    ! [X14,X12,X13] :
      ( r1_tarski(k4_xboole_0(X12,X13),X14)
      | ~ r1_tarski(X12,X13) ) ),
    inference(subsumption_resolution,[],[f703,f35])).

fof(f703,plain,(
    ! [X14,X12,X13] :
      ( r1_tarski(k4_xboole_0(X12,X13),X14)
      | ~ r1_tarski(X12,X13)
      | ~ r1_tarski(k1_xboole_0,X14) ) ),
    inference(superposition,[],[f300,f346])).

fof(f346,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f324,f318])).

fof(f318,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(resolution,[],[f316,f69])).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f65,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f65,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f46,f35])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f316,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f310,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f310,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f74,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f74,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k4_xboole_0(X2,X3))
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f324,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[],[f318,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f300,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X2,X0)),X3),X1)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f58,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f47,f37])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f37,f37])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f239,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k4_xboole_0(X3,k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X2))
      | r1_tarski(X3,k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2)))) ) ),
    inference(superposition,[],[f57,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f44,f37,f37])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f48,f37])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1701,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(resolution,[],[f307,f52])).

fof(f52,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f34,f37,f37,f37])).

fof(f34,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f29])).

fof(f307,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r1_tarski(k3_tarski(k2_tarski(X8,X9)),k2_zfmisc_1(k3_tarski(k2_tarski(X5,X7)),X6))
      | ~ r1_tarski(X9,k2_zfmisc_1(X7,X6))
      | ~ r1_tarski(X8,k2_zfmisc_1(X5,X6)) ) ),
    inference(superposition,[],[f58,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f43,f37,f37])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f1681,plain,(
    ! [X0] : r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(X0,sK5)))) ),
    inference(resolution,[],[f1650,f239])).

fof(f1650,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),k2_zfmisc_1(sK4,sK5)) ),
    inference(superposition,[],[f1159,f346])).

fof(f1159,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(sK1,X5),k2_zfmisc_1(k3_tarski(k2_tarski(sK4,X6)),sK5)) ),
    inference(subsumption_resolution,[],[f1134,f35])).

fof(f1134,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X6,sK5))
      | r1_tarski(k4_xboole_0(sK1,X5),k2_zfmisc_1(k3_tarski(k2_tarski(sK4,X6)),sK5)) ) ),
    inference(superposition,[],[f263,f922])).

fof(f922,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,X0),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f756,f36])).

fof(f756,plain,(
    ! [X38] :
      ( ~ r1_tarski(X38,sK1)
      | k1_xboole_0 = k4_xboole_0(X38,k2_zfmisc_1(sK4,sK5)) ) ),
    inference(resolution,[],[f723,f102])).

fof(f102,plain,(
    ! [X12] :
      ( r1_tarski(X12,k2_zfmisc_1(sK4,sK5))
      | ~ r1_tarski(X12,sK1) ) ),
    inference(resolution,[],[f50,f33])).

fof(f33,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f263,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(k4_xboole_0(X8,k2_zfmisc_1(X5,X6)),k2_zfmisc_1(X7,X6))
      | r1_tarski(X8,k2_zfmisc_1(k3_tarski(k2_tarski(X5,X7)),X6)) ) ),
    inference(superposition,[],[f57,f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:12:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (27961)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (27977)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (27963)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (27976)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (27984)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (27969)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.53  % (27955)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.53  % (27968)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.27/0.53  % (27956)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.53  % (27956)Refutation not found, incomplete strategy% (27956)------------------------------
% 1.27/0.53  % (27956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (27956)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (27956)Memory used [KB]: 1663
% 1.27/0.53  % (27956)Time elapsed: 0.125 s
% 1.27/0.53  % (27956)------------------------------
% 1.27/0.53  % (27956)------------------------------
% 1.27/0.54  % (27981)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.54  % (27958)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.54  % (27979)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.43/0.54  % (27980)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.54  % (27971)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.55  % (27957)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.43/0.55  % (27972)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.43/0.55  % (27973)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.55  % (27960)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.43/0.55  % (27964)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.55  % (27966)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.55  % (27959)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.43/0.56  % (27983)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.43/0.56  % (27965)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.56  % (27982)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.57  % (27974)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.58  % (27967)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.58  % (27975)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.43/0.58  % (27978)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.58  % (27970)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.59  % (27962)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.03/0.63  % (27961)Refutation found. Thanks to Tanya!
% 2.03/0.63  % SZS status Theorem for theBenchmark
% 2.03/0.63  % SZS output start Proof for theBenchmark
% 2.03/0.63  fof(f1723,plain,(
% 2.03/0.63    $false),
% 2.03/0.63    inference(resolution,[],[f1681,f1720])).
% 2.03/0.63  fof(f1720,plain,(
% 2.03/0.63    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5))))),
% 2.03/0.63    inference(subsumption_resolution,[],[f1701,f954])).
% 2.03/0.63  fof(f954,plain,(
% 2.03/0.63    ( ! [X16] : (r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X16))))) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f945,f35])).
% 2.03/0.63  fof(f35,plain,(
% 2.03/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f6])).
% 2.03/0.63  fof(f6,axiom,(
% 2.03/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.03/0.63  fof(f945,plain,(
% 2.03/0.63    ( ! [X16] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,X16)) | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X16))))) )),
% 2.03/0.63    inference(superposition,[],[f239,f758])).
% 2.03/0.63  fof(f758,plain,(
% 2.03/0.63    k1_xboole_0 = k4_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.03/0.63    inference(resolution,[],[f723,f32])).
% 2.03/0.63  fof(f32,plain,(
% 2.03/0.63    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.03/0.63    inference(cnf_transformation,[],[f29])).
% 2.03/0.63  fof(f29,plain,(
% 2.03/0.63    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f28])).
% 2.03/0.63  fof(f28,plain,(
% 2.03/0.63    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f17,plain,(
% 2.03/0.63    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 2.03/0.63    inference(flattening,[],[f16])).
% 2.03/0.63  fof(f16,plain,(
% 2.03/0.63    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 2.03/0.63    inference(ennf_transformation,[],[f15])).
% 2.03/0.63  fof(f15,negated_conjecture,(
% 2.03/0.63    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 2.03/0.63    inference(negated_conjecture,[],[f14])).
% 2.03/0.63  fof(f14,conjecture,(
% 2.03/0.63    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 2.03/0.63  fof(f723,plain,(
% 2.03/0.63    ( ! [X35,X34] : (~r1_tarski(X34,X35) | k1_xboole_0 = k4_xboole_0(X34,X35)) )),
% 2.03/0.63    inference(resolution,[],[f712,f72])).
% 2.03/0.63  fof(f72,plain,(
% 2.03/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.03/0.63    inference(resolution,[],[f42,f35])).
% 2.03/0.63  fof(f42,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f31])).
% 2.03/0.63  fof(f31,plain,(
% 2.03/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.63    inference(flattening,[],[f30])).
% 2.03/0.63  fof(f30,plain,(
% 2.03/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.63    inference(nnf_transformation,[],[f2])).
% 2.03/0.63  fof(f2,axiom,(
% 2.03/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.03/0.63  fof(f712,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,X1)) )),
% 2.03/0.63    inference(global_subsumption,[],[f711])).
% 2.03/0.63  fof(f711,plain,(
% 2.03/0.63    ( ! [X14,X12,X13] : (r1_tarski(k4_xboole_0(X12,X13),X14) | ~r1_tarski(X12,X13)) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f703,f35])).
% 2.03/0.63  fof(f703,plain,(
% 2.03/0.63    ( ! [X14,X12,X13] : (r1_tarski(k4_xboole_0(X12,X13),X14) | ~r1_tarski(X12,X13) | ~r1_tarski(k1_xboole_0,X14)) )),
% 2.03/0.63    inference(superposition,[],[f300,f346])).
% 2.03/0.63  fof(f346,plain,(
% 2.03/0.63    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 2.03/0.63    inference(forward_demodulation,[],[f324,f318])).
% 2.03/0.63  fof(f318,plain,(
% 2.03/0.63    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.03/0.63    inference(resolution,[],[f316,f69])).
% 2.03/0.63  fof(f69,plain,(
% 2.03/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.03/0.63    inference(resolution,[],[f65,f39])).
% 2.03/0.63  fof(f39,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f18])).
% 2.03/0.63  fof(f18,plain,(
% 2.03/0.63    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.03/0.63    inference(ennf_transformation,[],[f1])).
% 2.03/0.63  fof(f1,axiom,(
% 2.03/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.03/0.63  fof(f65,plain,(
% 2.03/0.63    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.03/0.63    inference(resolution,[],[f46,f35])).
% 2.03/0.63  fof(f46,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f19])).
% 2.03/0.63  fof(f19,plain,(
% 2.03/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.03/0.63    inference(ennf_transformation,[],[f3])).
% 2.03/0.63  fof(f3,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.03/0.63  fof(f316,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f310,f59])).
% 2.03/0.63  fof(f59,plain,(
% 2.03/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.03/0.63    inference(equality_resolution,[],[f41])).
% 2.03/0.63  fof(f41,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f31])).
% 2.03/0.63  fof(f310,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X0)) )),
% 2.03/0.63    inference(resolution,[],[f74,f49])).
% 2.03/0.63  fof(f49,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f23])).
% 2.03/0.63  fof(f23,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 2.03/0.63    inference(flattening,[],[f22])).
% 2.03/0.63  fof(f22,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.03/0.63    inference(ennf_transformation,[],[f11])).
% 2.03/0.63  fof(f11,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 2.03/0.63  fof(f74,plain,(
% 2.03/0.63    ( ! [X2,X3] : (~r1_tarski(X2,k4_xboole_0(X2,X3)) | k4_xboole_0(X2,X3) = X2) )),
% 2.03/0.63    inference(resolution,[],[f42,f36])).
% 2.03/0.63  fof(f36,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f7])).
% 2.03/0.63  fof(f7,axiom,(
% 2.03/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.03/0.63  fof(f324,plain,(
% 2.03/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_tarski(k2_tarski(X0,k1_xboole_0))) )),
% 2.03/0.63    inference(superposition,[],[f318,f53])).
% 2.03/0.63  fof(f53,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) )),
% 2.03/0.63    inference(definition_unfolding,[],[f38,f37])).
% 2.03/0.63  fof(f37,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f12])).
% 2.03/0.63  fof(f12,axiom,(
% 2.03/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.03/0.63  fof(f38,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f8])).
% 2.03/0.63  fof(f8,axiom,(
% 2.03/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.03/0.63  fof(f300,plain,(
% 2.03/0.63    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X2,X0)),X3),X1) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.03/0.63    inference(resolution,[],[f58,f56])).
% 2.03/0.63  fof(f56,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.03/0.63    inference(definition_unfolding,[],[f47,f37])).
% 2.03/0.63  fof(f47,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f20])).
% 2.03/0.63  fof(f20,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.03/0.63    inference(ennf_transformation,[],[f9])).
% 2.03/0.63  fof(f9,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.03/0.63  fof(f58,plain,(
% 2.03/0.63    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.03/0.63    inference(definition_unfolding,[],[f51,f37,f37])).
% 2.03/0.63  fof(f51,plain,(
% 2.03/0.63    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f27])).
% 2.03/0.63  fof(f27,plain,(
% 2.03/0.63    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.03/0.63    inference(flattening,[],[f26])).
% 2.03/0.63  fof(f26,plain,(
% 2.03/0.63    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.03/0.63    inference(ennf_transformation,[],[f4])).
% 2.03/0.63  fof(f4,axiom,(
% 2.03/0.63    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
% 2.03/0.63  fof(f239,plain,(
% 2.03/0.63    ( ! [X2,X0,X3,X1] : (~r1_tarski(k4_xboole_0(X3,k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X2)) | r1_tarski(X3,k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2))))) )),
% 2.03/0.63    inference(superposition,[],[f57,f54])).
% 2.03/0.63  fof(f54,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 2.03/0.63    inference(definition_unfolding,[],[f44,f37,f37])).
% 2.03/0.63  fof(f44,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f13])).
% 2.03/0.63  fof(f13,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 2.03/0.63  fof(f57,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.03/0.63    inference(definition_unfolding,[],[f48,f37])).
% 2.03/0.63  fof(f48,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f21])).
% 2.03/0.63  fof(f21,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.03/0.63    inference(ennf_transformation,[],[f10])).
% 2.03/0.63  fof(f10,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.03/0.63  fof(f1701,plain,(
% 2.03/0.63    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))),
% 2.03/0.63    inference(resolution,[],[f307,f52])).
% 2.03/0.63  fof(f52,plain,(
% 2.03/0.63    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 2.03/0.63    inference(definition_unfolding,[],[f34,f37,f37,f37])).
% 2.03/0.63  fof(f34,plain,(
% 2.03/0.63    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 2.03/0.63    inference(cnf_transformation,[],[f29])).
% 2.03/0.63  fof(f307,plain,(
% 2.03/0.63    ( ! [X6,X8,X7,X5,X9] : (r1_tarski(k3_tarski(k2_tarski(X8,X9)),k2_zfmisc_1(k3_tarski(k2_tarski(X5,X7)),X6)) | ~r1_tarski(X9,k2_zfmisc_1(X7,X6)) | ~r1_tarski(X8,k2_zfmisc_1(X5,X6))) )),
% 2.03/0.63    inference(superposition,[],[f58,f55])).
% 2.03/0.63  fof(f55,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 2.03/0.63    inference(definition_unfolding,[],[f43,f37,f37])).
% 2.03/0.63  fof(f43,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f13])).
% 2.03/0.63  fof(f1681,plain,(
% 2.03/0.63    ( ! [X0] : (r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(X0,sK5))))) )),
% 2.03/0.63    inference(resolution,[],[f1650,f239])).
% 2.03/0.63  fof(f1650,plain,(
% 2.03/0.63    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),k2_zfmisc_1(sK4,sK5))) )),
% 2.03/0.63    inference(superposition,[],[f1159,f346])).
% 2.03/0.63  fof(f1159,plain,(
% 2.03/0.63    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(sK1,X5),k2_zfmisc_1(k3_tarski(k2_tarski(sK4,X6)),sK5))) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f1134,f35])).
% 2.03/0.63  fof(f1134,plain,(
% 2.03/0.63    ( ! [X6,X5] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X6,sK5)) | r1_tarski(k4_xboole_0(sK1,X5),k2_zfmisc_1(k3_tarski(k2_tarski(sK4,X6)),sK5))) )),
% 2.03/0.63    inference(superposition,[],[f263,f922])).
% 2.03/0.63  fof(f922,plain,(
% 2.03/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,X0),k2_zfmisc_1(sK4,sK5))) )),
% 2.03/0.63    inference(resolution,[],[f756,f36])).
% 2.03/0.63  fof(f756,plain,(
% 2.03/0.63    ( ! [X38] : (~r1_tarski(X38,sK1) | k1_xboole_0 = k4_xboole_0(X38,k2_zfmisc_1(sK4,sK5))) )),
% 2.03/0.63    inference(resolution,[],[f723,f102])).
% 2.03/0.63  fof(f102,plain,(
% 2.03/0.63    ( ! [X12] : (r1_tarski(X12,k2_zfmisc_1(sK4,sK5)) | ~r1_tarski(X12,sK1)) )),
% 2.03/0.63    inference(resolution,[],[f50,f33])).
% 2.03/0.63  fof(f33,plain,(
% 2.03/0.63    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 2.03/0.63    inference(cnf_transformation,[],[f29])).
% 2.03/0.63  fof(f50,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f25])).
% 2.03/0.63  fof(f25,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.03/0.63    inference(flattening,[],[f24])).
% 2.03/0.63  fof(f24,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.03/0.63    inference(ennf_transformation,[],[f5])).
% 2.03/0.63  fof(f5,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.03/0.63  fof(f263,plain,(
% 2.03/0.63    ( ! [X6,X8,X7,X5] : (~r1_tarski(k4_xboole_0(X8,k2_zfmisc_1(X5,X6)),k2_zfmisc_1(X7,X6)) | r1_tarski(X8,k2_zfmisc_1(k3_tarski(k2_tarski(X5,X7)),X6))) )),
% 2.03/0.63    inference(superposition,[],[f57,f55])).
% 2.03/0.63  % SZS output end Proof for theBenchmark
% 2.03/0.63  % (27961)------------------------------
% 2.03/0.63  % (27961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.63  % (27961)Termination reason: Refutation
% 2.03/0.63  
% 2.03/0.63  % (27961)Memory used [KB]: 12281
% 2.03/0.63  % (27961)Time elapsed: 0.218 s
% 2.03/0.63  % (27961)------------------------------
% 2.03/0.63  % (27961)------------------------------
% 2.03/0.65  % (27954)Success in time 0.293 s
%------------------------------------------------------------------------------
