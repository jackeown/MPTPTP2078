%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:58 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  141 (1348 expanded)
%              Number of leaves         :   26 ( 387 expanded)
%              Depth                    :   29
%              Number of atoms          :  284 (2541 expanded)
%              Number of equality atoms :  138 (1739 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f647,plain,(
    $false ),
    inference(subsumption_resolution,[],[f646,f622])).

fof(f622,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(trivial_inequality_removal,[],[f616])).

fof(f616,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[],[f81,f552])).

fof(f552,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f533,f263])).

fof(f263,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f150,f147])).

fof(f147,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f87,f143])).

fof(f143,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f107,f140])).

fof(f140,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f109,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f123,f138])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f131,f137])).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f133,f136])).

fof(f136,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f134,f135])).

fof(f135,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f134,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f133,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f131,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f123,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f109,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f107,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f87,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f150,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f111,f143])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f533,plain,(
    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f532,f80])).

fof(f80,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f38])).

fof(f38,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f532,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f530,f176])).

fof(f176,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f105,f165])).

fof(f165,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f105,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f530,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f524,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f524,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f516,f165])).

fof(f516,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f90,f500])).

fof(f500,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f430,f80])).

fof(f430,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f429,f321])).

fof(f321,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f320,f83])).

fof(f83,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f320,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f316,f176])).

fof(f316,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f94,f82])).

fof(f82,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f429,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(trivial_inequality_removal,[],[f428])).

fof(f428,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f152,f146])).

fof(f146,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f85,f142])).

fof(f142,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f110,f141])).

fof(f141,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f108,f140])).

fof(f108,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f110,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f152,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f119,f142])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f90,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f81,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f646,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f645,f145])).

fof(f145,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f84,f141])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f645,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f644,f166])).

fof(f166,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f75])).

fof(f644,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) ),
    inference(backward_demodulation,[],[f570,f643])).

fof(f643,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f640,f424])).

fof(f424,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f419,f358])).

fof(f358,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f356,f263])).

fof(f356,plain,(
    r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f355,f176])).

fof(f355,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f347,f112])).

fof(f347,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f339,f165])).

fof(f339,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f90,f328])).

fof(f328,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f327,f176])).

fof(f327,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f325,f163])).

fof(f163,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
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

fof(f325,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f321,f83])).

fof(f419,plain,(
    k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),sK0) = k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f410,f176])).

fof(f410,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X2,k1_xboole_0),sK0) = k5_relat_1(X2,k5_relat_1(k1_xboole_0,sK0)) ) ),
    inference(resolution,[],[f408,f176])).

fof(f408,plain,(
    ! [X17,X16] :
      ( ~ v1_relat_1(X17)
      | k5_relat_1(k5_relat_1(X16,X17),sK0) = k5_relat_1(X16,k5_relat_1(X17,sK0))
      | ~ v1_relat_1(X16) ) ),
    inference(resolution,[],[f96,f80])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f640,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f596,f569])).

fof(f569,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f471,f554])).

fof(f554,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) ),
    inference(backward_demodulation,[],[f423,f552])).

fof(f423,plain,(
    k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f410,f80])).

fof(f471,plain,(
    v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) ),
    inference(subsumption_resolution,[],[f470,f80])).

fof(f470,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f468,f176])).

fof(f468,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f464,f112])).

fof(f464,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) ),
    inference(subsumption_resolution,[],[f459,f80])).

fof(f459,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f112,f423])).

fof(f596,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X1)) ) ),
    inference(forward_demodulation,[],[f595,f82])).

fof(f595,plain,(
    ! [X1] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f594,f552])).

fof(f594,plain,(
    ! [X1] :
      ( k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f563,f176])).

fof(f563,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X1))
      | ~ v1_relat_1(X1) ) ),
    inference(backward_demodulation,[],[f525,f552])).

fof(f525,plain,(
    ! [X1] :
      ( k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f518,f429])).

fof(f518,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ) ),
    inference(superposition,[],[f95,f500])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f570,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) ),
    inference(backward_demodulation,[],[f474,f554])).

fof(f474,plain,(
    k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)))))) ),
    inference(resolution,[],[f471,f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f91,f141])).

fof(f91,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (5846)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.49  % (5854)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.50  % (5837)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (5863)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (5862)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (5835)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (5844)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (5840)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (5843)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (5845)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (5839)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (5845)Refutation not found, incomplete strategy% (5845)------------------------------
% 0.20/0.51  % (5845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5845)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5845)Memory used [KB]: 10874
% 0.20/0.51  % (5845)Time elapsed: 0.117 s
% 0.20/0.51  % (5845)------------------------------
% 0.20/0.51  % (5845)------------------------------
% 0.20/0.52  % (5852)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (5861)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (5859)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (5838)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (5855)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (5858)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (5856)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (5848)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (5847)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (5860)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.53  % (5836)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.53  % (5841)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.53  % (5853)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.53  % (5864)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.53  % (5857)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.33/0.54  % (5863)Refutation not found, incomplete strategy% (5863)------------------------------
% 1.33/0.54  % (5863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (5863)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (5863)Memory used [KB]: 10874
% 1.33/0.54  % (5863)Time elapsed: 0.143 s
% 1.33/0.54  % (5863)------------------------------
% 1.33/0.54  % (5863)------------------------------
% 1.33/0.54  % (5842)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.54  % (5849)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.33/0.54  % (5851)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.33/0.54  % (5851)Refutation not found, incomplete strategy% (5851)------------------------------
% 1.33/0.54  % (5851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (5851)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (5851)Memory used [KB]: 10746
% 1.33/0.54  % (5851)Time elapsed: 0.150 s
% 1.33/0.54  % (5851)------------------------------
% 1.33/0.54  % (5851)------------------------------
% 1.33/0.54  % (5850)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.57  % (5857)Refutation found. Thanks to Tanya!
% 1.48/0.57  % SZS status Theorem for theBenchmark
% 1.48/0.57  % SZS output start Proof for theBenchmark
% 1.48/0.57  fof(f647,plain,(
% 1.48/0.57    $false),
% 1.48/0.57    inference(subsumption_resolution,[],[f646,f622])).
% 1.48/0.57  fof(f622,plain,(
% 1.48/0.57    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.48/0.57    inference(trivial_inequality_removal,[],[f616])).
% 1.48/0.57  fof(f616,plain,(
% 1.48/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.48/0.57    inference(superposition,[],[f81,f552])).
% 1.48/0.57  fof(f552,plain,(
% 1.48/0.57    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.48/0.57    inference(resolution,[],[f533,f263])).
% 1.48/0.57  fof(f263,plain,(
% 1.48/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.48/0.57    inference(superposition,[],[f150,f147])).
% 1.48/0.57  fof(f147,plain,(
% 1.48/0.57    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.48/0.57    inference(definition_unfolding,[],[f87,f143])).
% 1.48/0.57  fof(f143,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f107,f140])).
% 1.48/0.57  fof(f140,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f109,f139])).
% 1.48/0.57  fof(f139,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f123,f138])).
% 1.48/0.57  fof(f138,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f131,f137])).
% 1.48/0.57  fof(f137,plain,(
% 1.48/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f133,f136])).
% 1.48/0.57  fof(f136,plain,(
% 1.48/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f134,f135])).
% 1.48/0.57  fof(f135,plain,(
% 1.48/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f16])).
% 1.48/0.57  fof(f16,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.48/0.57  fof(f134,plain,(
% 1.48/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f15])).
% 1.48/0.57  fof(f15,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.48/0.57  fof(f133,plain,(
% 1.48/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f14])).
% 1.48/0.57  fof(f14,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.48/0.57  fof(f131,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f13])).
% 1.48/0.57  fof(f13,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.48/0.57  fof(f123,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f12])).
% 1.48/0.57  fof(f12,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.57  fof(f109,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f11])).
% 1.48/0.57  fof(f11,axiom,(
% 1.48/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.57  fof(f107,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f17])).
% 1.48/0.57  fof(f17,axiom,(
% 1.48/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.48/0.57  fof(f87,plain,(
% 1.48/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f6])).
% 1.48/0.57  fof(f6,axiom,(
% 1.48/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.48/0.57  fof(f150,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f111,f143])).
% 1.48/0.57  fof(f111,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f57])).
% 1.48/0.57  fof(f57,plain,(
% 1.48/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f5])).
% 1.48/0.57  fof(f5,axiom,(
% 1.48/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.48/0.57  fof(f533,plain,(
% 1.48/0.57    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.48/0.57    inference(subsumption_resolution,[],[f532,f80])).
% 1.48/0.57  fof(f80,plain,(
% 1.48/0.57    v1_relat_1(sK0)),
% 1.48/0.57    inference(cnf_transformation,[],[f62])).
% 1.48/0.57  fof(f62,plain,(
% 1.48/0.57    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f61])).
% 1.48/0.57  fof(f61,plain,(
% 1.48/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.48/0.57    introduced(choice_axiom,[])).
% 1.48/0.57  fof(f41,plain,(
% 1.48/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.48/0.57    inference(ennf_transformation,[],[f39])).
% 1.48/0.57  fof(f39,negated_conjecture,(
% 1.48/0.57    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.48/0.57    inference(negated_conjecture,[],[f38])).
% 1.48/0.57  fof(f38,conjecture,(
% 1.48/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.48/0.57  fof(f532,plain,(
% 1.48/0.57    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.48/0.57    inference(subsumption_resolution,[],[f530,f176])).
% 1.48/0.57  fof(f176,plain,(
% 1.48/0.57    v1_relat_1(k1_xboole_0)),
% 1.48/0.57    inference(superposition,[],[f105,f165])).
% 1.48/0.57  fof(f165,plain,(
% 1.48/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.48/0.57    inference(equality_resolution,[],[f118])).
% 1.48/0.57  fof(f118,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.48/0.57    inference(cnf_transformation,[],[f75])).
% 1.48/0.57  fof(f75,plain,(
% 1.48/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.48/0.57    inference(flattening,[],[f74])).
% 1.48/0.57  fof(f74,plain,(
% 1.48/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.48/0.57    inference(nnf_transformation,[],[f18])).
% 1.48/0.57  fof(f18,axiom,(
% 1.48/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.48/0.57  fof(f105,plain,(
% 1.48/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f28])).
% 1.48/0.57  fof(f28,axiom,(
% 1.48/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.48/0.57  fof(f530,plain,(
% 1.48/0.57    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.48/0.57    inference(resolution,[],[f524,f112])).
% 1.48/0.57  fof(f112,plain,(
% 1.48/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f59])).
% 1.48/0.57  fof(f59,plain,(
% 1.48/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(flattening,[],[f58])).
% 1.48/0.57  fof(f58,plain,(
% 1.48/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.48/0.57    inference(ennf_transformation,[],[f27])).
% 1.48/0.57  fof(f27,axiom,(
% 1.48/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.48/0.57  fof(f524,plain,(
% 1.48/0.57    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.48/0.57    inference(forward_demodulation,[],[f516,f165])).
% 1.48/0.57  fof(f516,plain,(
% 1.48/0.57    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.48/0.57    inference(superposition,[],[f90,f500])).
% 1.48/0.57  fof(f500,plain,(
% 1.48/0.57    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.48/0.57    inference(resolution,[],[f430,f80])).
% 1.48/0.57  fof(f430,plain,(
% 1.48/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 1.48/0.57    inference(resolution,[],[f429,f321])).
% 1.48/0.57  fof(f321,plain,(
% 1.48/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f320,f83])).
% 1.48/0.57  fof(f83,plain,(
% 1.48/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.48/0.57    inference(cnf_transformation,[],[f37])).
% 1.48/0.57  fof(f37,axiom,(
% 1.48/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.48/0.57  fof(f320,plain,(
% 1.48/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f316,f176])).
% 1.48/0.57  fof(f316,plain,(
% 1.48/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.48/0.57    inference(superposition,[],[f94,f82])).
% 1.48/0.57  fof(f82,plain,(
% 1.48/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.48/0.57    inference(cnf_transformation,[],[f37])).
% 1.48/0.57  fof(f94,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f47])).
% 1.48/0.57  fof(f47,plain,(
% 1.48/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(flattening,[],[f46])).
% 1.48/0.57  fof(f46,plain,(
% 1.48/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(ennf_transformation,[],[f33])).
% 1.48/0.57  fof(f33,axiom,(
% 1.48/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 1.48/0.57  fof(f429,plain,(
% 1.48/0.57    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.48/0.57    inference(trivial_inequality_removal,[],[f428])).
% 1.48/0.57  fof(f428,plain,(
% 1.48/0.57    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X2)) )),
% 1.48/0.57    inference(superposition,[],[f152,f146])).
% 1.48/0.57  fof(f146,plain,(
% 1.48/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f85,f142])).
% 1.48/0.57  fof(f142,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f110,f141])).
% 1.48/0.57  fof(f141,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f108,f140])).
% 1.48/0.57  fof(f108,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f23])).
% 1.48/0.57  fof(f23,axiom,(
% 1.48/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.48/0.57  fof(f110,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f4])).
% 1.48/0.57  fof(f4,axiom,(
% 1.48/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.48/0.57  fof(f85,plain,(
% 1.48/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f8])).
% 1.48/0.57  fof(f8,axiom,(
% 1.48/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.48/0.57  fof(f152,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f119,f142])).
% 1.48/0.57  fof(f119,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f76])).
% 1.48/0.57  fof(f76,plain,(
% 1.48/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.48/0.57    inference(nnf_transformation,[],[f3])).
% 1.48/0.57  fof(f3,axiom,(
% 1.48/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.48/0.57  fof(f90,plain,(
% 1.48/0.57    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f43])).
% 1.48/0.57  fof(f43,plain,(
% 1.48/0.57    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(ennf_transformation,[],[f29])).
% 1.48/0.57  fof(f29,axiom,(
% 1.48/0.57    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.48/0.57  fof(f81,plain,(
% 1.48/0.57    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.48/0.57    inference(cnf_transformation,[],[f62])).
% 1.48/0.57  fof(f646,plain,(
% 1.48/0.57    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.48/0.57    inference(forward_demodulation,[],[f645,f145])).
% 1.48/0.57  fof(f145,plain,(
% 1.48/0.57    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f84,f141])).
% 1.48/0.57  fof(f84,plain,(
% 1.48/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f7])).
% 1.48/0.57  fof(f7,axiom,(
% 1.48/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.48/0.57  fof(f645,plain,(
% 1.48/0.57    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0))),
% 1.48/0.57    inference(forward_demodulation,[],[f644,f166])).
% 1.48/0.57  fof(f166,plain,(
% 1.48/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.48/0.57    inference(equality_resolution,[],[f117])).
% 1.48/0.57  fof(f117,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f75])).
% 1.48/0.57  fof(f644,plain,(
% 1.48/0.57    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))),
% 1.48/0.57    inference(backward_demodulation,[],[f570,f643])).
% 1.48/0.57  fof(f643,plain,(
% 1.48/0.57    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.57    inference(forward_demodulation,[],[f640,f424])).
% 1.48/0.57  fof(f424,plain,(
% 1.48/0.57    k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.57    inference(forward_demodulation,[],[f419,f358])).
% 1.48/0.57  fof(f358,plain,(
% 1.48/0.57    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.48/0.57    inference(resolution,[],[f356,f263])).
% 1.48/0.57  fof(f356,plain,(
% 1.48/0.57    r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.48/0.57    inference(subsumption_resolution,[],[f355,f176])).
% 1.48/0.57  fof(f355,plain,(
% 1.48/0.57    r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f353])).
% 1.48/0.57  fof(f353,plain,(
% 1.48/0.57    r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.48/0.57    inference(resolution,[],[f347,f112])).
% 1.48/0.57  fof(f347,plain,(
% 1.48/0.57    ~v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) | r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.48/0.57    inference(forward_demodulation,[],[f339,f165])).
% 1.48/0.57  fof(f339,plain,(
% 1.48/0.57    r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))),
% 1.48/0.57    inference(superposition,[],[f90,f328])).
% 1.48/0.57  fof(f328,plain,(
% 1.48/0.57    k1_xboole_0 = k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))),
% 1.48/0.57    inference(subsumption_resolution,[],[f327,f176])).
% 1.48/0.57  fof(f327,plain,(
% 1.48/0.57    k1_xboole_0 = k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.48/0.57    inference(subsumption_resolution,[],[f325,f163])).
% 1.48/0.57  fof(f163,plain,(
% 1.48/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/0.57    inference(equality_resolution,[],[f114])).
% 1.48/0.57  fof(f114,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.48/0.57    inference(cnf_transformation,[],[f73])).
% 1.48/0.57  fof(f73,plain,(
% 1.48/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.57    inference(flattening,[],[f72])).
% 1.48/0.57  fof(f72,plain,(
% 1.48/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.57    inference(nnf_transformation,[],[f2])).
% 1.48/0.57  fof(f2,axiom,(
% 1.48/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.57  fof(f325,plain,(
% 1.48/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.48/0.57    inference(superposition,[],[f321,f83])).
% 1.48/0.57  fof(f419,plain,(
% 1.48/0.57    k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),sK0) = k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.57    inference(resolution,[],[f410,f176])).
% 1.48/0.57  fof(f410,plain,(
% 1.48/0.57    ( ! [X2] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X2,k1_xboole_0),sK0) = k5_relat_1(X2,k5_relat_1(k1_xboole_0,sK0))) )),
% 1.48/0.57    inference(resolution,[],[f408,f176])).
% 1.48/0.57  fof(f408,plain,(
% 1.48/0.57    ( ! [X17,X16] : (~v1_relat_1(X17) | k5_relat_1(k5_relat_1(X16,X17),sK0) = k5_relat_1(X16,k5_relat_1(X17,sK0)) | ~v1_relat_1(X16)) )),
% 1.48/0.57    inference(resolution,[],[f96,f80])).
% 1.48/0.57  fof(f96,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f50])).
% 1.48/0.57  fof(f50,plain,(
% 1.48/0.57    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.57    inference(ennf_transformation,[],[f36])).
% 1.48/0.57  fof(f36,axiom,(
% 1.48/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.48/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.48/0.57  fof(f640,plain,(
% 1.48/0.57    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)))),
% 1.48/0.57    inference(resolution,[],[f596,f569])).
% 1.48/0.57  fof(f569,plain,(
% 1.48/0.57    v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.57    inference(backward_demodulation,[],[f471,f554])).
% 1.48/0.57  fof(f554,plain,(
% 1.48/0.57    k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.57    inference(backward_demodulation,[],[f423,f552])).
% 1.48/0.57  fof(f423,plain,(
% 1.48/0.57    k5_relat_1(k5_relat_1(sK0,k1_xboole_0),sK0) = k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),
% 1.48/0.57    inference(resolution,[],[f410,f80])).
% 1.48/0.57  fof(f471,plain,(
% 1.48/0.57    v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)))),
% 1.48/0.57    inference(subsumption_resolution,[],[f470,f80])).
% 1.48/0.57  fof(f470,plain,(
% 1.48/0.57    v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(sK0)),
% 1.48/0.57    inference(subsumption_resolution,[],[f468,f176])).
% 1.48/0.57  fof(f468,plain,(
% 1.48/0.57    v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.48/0.57    inference(resolution,[],[f464,f112])).
% 1.48/0.57  fof(f464,plain,(
% 1.48/0.57    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)))),
% 1.48/0.57    inference(subsumption_resolution,[],[f459,f80])).
% 1.48/0.57  fof(f459,plain,(
% 1.48/0.57    v1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.48/0.57    inference(superposition,[],[f112,f423])).
% 1.48/0.57  fof(f596,plain,(
% 1.48/0.57    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X1))) )),
% 1.48/0.57    inference(forward_demodulation,[],[f595,f82])).
% 1.48/0.57  fof(f595,plain,(
% 1.48/0.57    ( ! [X1] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X1)) | ~v1_relat_1(X1)) )),
% 1.48/0.57    inference(forward_demodulation,[],[f594,f552])).
% 1.48/0.57  fof(f594,plain,(
% 1.48/0.57    ( ! [X1] : (k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X1)) | ~v1_relat_1(X1)) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f563,f176])).
% 1.48/0.57  fof(f563,plain,(
% 1.48/0.57    ( ! [X1] : (~v1_relat_1(k1_xboole_0) | k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X1)) | ~v1_relat_1(X1)) )),
% 1.48/0.57    inference(backward_demodulation,[],[f525,f552])).
% 1.48/0.57  fof(f525,plain,(
% 1.48/0.57    ( ! [X1] : (k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f518,f429])).
% 1.48/0.57  fof(f518,plain,(
% 1.48/0.57    ( ! [X1] : (~r1_tarski(k1_xboole_0,k1_relat_1(X1)) | k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_relat_1(k5_relat_1(k5_relat_1(sK0,k1_xboole_0),X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))) )),
% 1.48/0.57    inference(superposition,[],[f95,f500])).
% 1.48/0.57  fof(f95,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f49])).
% 1.48/0.58  fof(f49,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(flattening,[],[f48])).
% 1.48/0.58  fof(f48,plain,(
% 1.48/0.58    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f32])).
% 1.48/0.58  fof(f32,axiom,(
% 1.48/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.48/0.58  fof(f570,plain,(
% 1.48/0.58    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))),
% 1.48/0.58    inference(backward_demodulation,[],[f474,f554])).
% 1.48/0.58  fof(f474,plain,(
% 1.48/0.58    k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)) = k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,sK0))))))),
% 1.48/0.58    inference(resolution,[],[f471,f148])).
% 1.48/0.58  fof(f148,plain,(
% 1.48/0.58    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 1.48/0.58    inference(definition_unfolding,[],[f91,f141])).
% 1.48/0.58  fof(f91,plain,(
% 1.48/0.58    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.48/0.58    inference(cnf_transformation,[],[f44])).
% 1.48/0.58  fof(f44,plain,(
% 1.48/0.58    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.48/0.58    inference(ennf_transformation,[],[f30])).
% 1.48/0.58  fof(f30,axiom,(
% 1.48/0.58    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.48/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 1.48/0.58  % SZS output end Proof for theBenchmark
% 1.48/0.58  % (5857)------------------------------
% 1.48/0.58  % (5857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (5857)Termination reason: Refutation
% 1.48/0.58  
% 1.48/0.58  % (5857)Memory used [KB]: 6780
% 1.48/0.58  % (5857)Time elapsed: 0.144 s
% 1.48/0.58  % (5857)------------------------------
% 1.48/0.58  % (5857)------------------------------
% 1.48/0.58  % (5834)Success in time 0.226 s
%------------------------------------------------------------------------------
