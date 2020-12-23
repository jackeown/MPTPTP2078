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
% DateTime   : Thu Dec  3 12:48:01 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 329 expanded)
%              Number of leaves         :   23 ( 100 expanded)
%              Depth                    :   19
%              Number of atoms          :  306 ( 720 expanded)
%              Number of equality atoms :   79 ( 300 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f630,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f42,f623,f186])).

fof(f186,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f185,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f185,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f184,f45])).

fof(f45,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f184,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f183,f84])).

fof(f84,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f82,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f40,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f72,f47])).

fof(f47,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f183,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f177,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f177,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f163,f46])).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f163,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | v1_xboole_0(k5_relat_1(X1,X2))
      | ~ v1_xboole_0(k1_relat_1(X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f161,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f161,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(k1_relat_1(X1))
      | v1_xboole_0(k5_relat_1(X1,X2))
      | ~ v1_relat_1(k5_relat_1(X1,X2))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f157,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f157,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(k1_relat_1(X3))
      | v1_xboole_0(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f152,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f152,plain,(
    ! [X3] :
      ( v1_xboole_0(X3)
      | ~ v1_xboole_0(k1_relat_1(X3))
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(X3),k2_relat_1(X3)))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f60,f108])).

fof(f108,plain,(
    ! [X1] :
      ( k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)) = X1
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f80,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f57,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f50,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f70,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f623,plain,(
    ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f616,f42])).

fof(f616,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f610,f336])).

fof(f336,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f335,f48])).

fof(f335,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f334,f46])).

fof(f334,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f333,f84])).

fof(f333,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f332,f42])).

fof(f332,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f330,f45])).

fof(f330,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f220,f89])).

fof(f89,plain,(
    ! [X2,X3] :
      ( k5_relat_1(X2,X3) = k1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_xboole_0(k5_relat_1(X2,X3)) ) ),
    inference(superposition,[],[f52,f75])).

fof(f75,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f45,f53])).

fof(f220,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f219,f48])).

fof(f219,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK0))
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f218,f45])).

fof(f218,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0))
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f217,f84])).

fof(f217,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f216,f42])).

fof(f216,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f207,f46])).

fof(f207,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f43,f86])).

fof(f86,plain,(
    ! [X2,X3] :
      ( k5_relat_1(X2,X3) = k2_relat_1(X3)
      | ~ r1_tarski(k1_relat_1(X3),k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_xboole_0(k5_relat_1(X2,X3)) ) ),
    inference(superposition,[],[f51,f74])).

fof(f74,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f46,f53])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f43,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f610,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f609,f44])).

fof(f609,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f608,f46])).

fof(f608,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
      | v1_xboole_0(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f607,f84])).

fof(f607,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
      | v1_xboole_0(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f600,f48])).

fof(f600,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
      | v1_xboole_0(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f328,f45])).

fof(f328,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(k1_relat_1(X9),k2_relat_1(X8))
      | ~ v1_xboole_0(k2_relat_1(X9))
      | v1_xboole_0(k5_relat_1(X8,X9))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f316,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f316,plain,(
    ! [X8,X9] :
      ( v1_xboole_0(k5_relat_1(X8,X9))
      | ~ v1_xboole_0(k2_relat_1(X9))
      | ~ r1_tarski(k1_relat_1(X9),k2_relat_1(X8))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(X8,X9)),k2_relat_1(X9))) ) ),
    inference(superposition,[],[f59,f131])).

fof(f131,plain,(
    ! [X2,X3] :
      ( k5_relat_1(X2,X3) = k2_zfmisc_1(k1_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3))
      | ~ r1_tarski(k1_relat_1(X3),k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3))) ) ),
    inference(superposition,[],[f102,f80])).

fof(f102,plain,(
    ! [X2,X1] :
      ( k5_relat_1(X1,X2) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))))
      | ~ r1_tarski(k1_relat_1(X2),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f96,f61])).

fof(f96,plain,(
    ! [X2,X1] :
      ( k5_relat_1(X1,X2) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))))
      | ~ v1_relat_1(k5_relat_1(X1,X2))
      | ~ r1_tarski(k1_relat_1(X2),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f71,f51])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:40:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (9152)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (9145)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (9142)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (9162)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (9159)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (9144)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (9140)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (9161)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (9168)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (9153)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (9141)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (9139)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (9160)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (9161)Refutation not found, incomplete strategy% (9161)------------------------------
% 0.22/0.54  % (9161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9161)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9161)Memory used [KB]: 10618
% 0.22/0.54  % (9161)Time elapsed: 0.059 s
% 0.22/0.54  % (9161)------------------------------
% 0.22/0.54  % (9161)------------------------------
% 0.22/0.54  % (9141)Refutation not found, incomplete strategy% (9141)------------------------------
% 0.22/0.54  % (9141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9141)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9141)Memory used [KB]: 10618
% 0.22/0.54  % (9141)Time elapsed: 0.114 s
% 0.22/0.54  % (9141)------------------------------
% 0.22/0.54  % (9141)------------------------------
% 0.22/0.54  % (9146)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (9164)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (9143)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (9165)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (9155)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (9163)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (9166)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (9156)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (9156)Refutation not found, incomplete strategy% (9156)------------------------------
% 0.22/0.55  % (9156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9156)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9156)Memory used [KB]: 10618
% 0.22/0.55  % (9156)Time elapsed: 0.129 s
% 0.22/0.55  % (9156)------------------------------
% 0.22/0.55  % (9156)------------------------------
% 0.22/0.55  % (9154)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (9154)Refutation not found, incomplete strategy% (9154)------------------------------
% 0.22/0.55  % (9154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9154)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9154)Memory used [KB]: 6140
% 0.22/0.55  % (9154)Time elapsed: 0.128 s
% 0.22/0.55  % (9154)------------------------------
% 0.22/0.55  % (9154)------------------------------
% 0.22/0.55  % (9167)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (9157)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (9147)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (9147)Refutation not found, incomplete strategy% (9147)------------------------------
% 0.22/0.55  % (9147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9147)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9147)Memory used [KB]: 10618
% 0.22/0.55  % (9147)Time elapsed: 0.139 s
% 0.22/0.55  % (9147)------------------------------
% 0.22/0.55  % (9147)------------------------------
% 0.22/0.56  % (9148)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (9149)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (9158)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (9150)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (9151)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.62/0.59  % (9168)Refutation found. Thanks to Tanya!
% 1.62/0.59  % SZS status Theorem for theBenchmark
% 1.62/0.59  % SZS output start Proof for theBenchmark
% 1.62/0.59  fof(f630,plain,(
% 1.62/0.59    $false),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f42,f623,f186])).
% 1.62/0.59  fof(f186,plain,(
% 1.62/0.59    ( ! [X0] : (v1_xboole_0(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f185,f44])).
% 1.62/0.59  fof(f44,plain,(
% 1.62/0.59    v1_xboole_0(k1_xboole_0)),
% 1.62/0.59    inference(cnf_transformation,[],[f1])).
% 1.62/0.59  fof(f1,axiom,(
% 1.62/0.59    v1_xboole_0(k1_xboole_0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.62/0.59  fof(f185,plain,(
% 1.62/0.59    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(forward_demodulation,[],[f184,f45])).
% 1.62/0.59  fof(f45,plain,(
% 1.62/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.62/0.59    inference(cnf_transformation,[],[f19])).
% 1.62/0.59  fof(f19,axiom,(
% 1.62/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.62/0.59  fof(f184,plain,(
% 1.62/0.59    ( ! [X0] : (v1_xboole_0(k5_relat_1(k1_xboole_0,X0)) | ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f183,f84])).
% 1.62/0.59  fof(f84,plain,(
% 1.62/0.59    v1_relat_1(k1_xboole_0)),
% 1.62/0.59    inference(resolution,[],[f82,f55])).
% 1.62/0.59  fof(f55,plain,(
% 1.62/0.59    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f41])).
% 1.62/0.59  fof(f41,plain,(
% 1.62/0.59    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f40,f39])).
% 1.62/0.59  fof(f39,plain,(
% 1.62/0.59    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f40,plain,(
% 1.62/0.59    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.62/0.59    inference(rectify,[],[f37])).
% 1.62/0.59  fof(f37,plain,(
% 1.62/0.59    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.62/0.59    inference(nnf_transformation,[],[f29])).
% 1.62/0.59  fof(f29,plain,(
% 1.62/0.59    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f14])).
% 1.62/0.59  fof(f14,axiom,(
% 1.62/0.59    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.62/0.59  fof(f82,plain,(
% 1.62/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.62/0.59    inference(resolution,[],[f72,f47])).
% 1.62/0.59  fof(f47,plain,(
% 1.62/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f5])).
% 1.62/0.59  fof(f5,axiom,(
% 1.62/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.62/0.59  fof(f72,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f63,f68])).
% 1.62/0.59  fof(f68,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f58,f67])).
% 1.62/0.59  fof(f67,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f62,f66])).
% 1.62/0.59  fof(f66,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f64,f65])).
% 1.62/0.59  fof(f65,plain,(
% 1.62/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f9])).
% 1.62/0.59  fof(f9,axiom,(
% 1.62/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.62/0.59  fof(f64,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f8])).
% 1.62/0.59  fof(f8,axiom,(
% 1.62/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.62/0.59  fof(f62,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f7])).
% 1.62/0.59  fof(f7,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.62/0.59  fof(f58,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f6])).
% 1.62/0.59  fof(f6,axiom,(
% 1.62/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.62/0.59  fof(f63,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f34])).
% 1.62/0.59  fof(f34,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.62/0.59    inference(ennf_transformation,[],[f12])).
% 1.62/0.59  fof(f12,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.62/0.59  fof(f183,plain,(
% 1.62/0.59    ( ! [X0] : (v1_xboole_0(k5_relat_1(k1_xboole_0,X0)) | ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f177,f48])).
% 1.62/0.59  fof(f48,plain,(
% 1.62/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f4])).
% 1.62/0.59  fof(f4,axiom,(
% 1.62/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.62/0.59  fof(f177,plain,(
% 1.62/0.59    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,X0)) | ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.62/0.59    inference(superposition,[],[f163,f46])).
% 1.62/0.59  fof(f46,plain,(
% 1.62/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.62/0.59    inference(cnf_transformation,[],[f19])).
% 1.62/0.59  fof(f163,plain,(
% 1.62/0.59    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | v1_xboole_0(k5_relat_1(X1,X2)) | ~v1_xboole_0(k1_relat_1(X1)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f161,f61])).
% 1.62/0.59  fof(f61,plain,(
% 1.62/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f33])).
% 1.62/0.59  fof(f33,plain,(
% 1.62/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(flattening,[],[f32])).
% 1.62/0.59  fof(f32,plain,(
% 1.62/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f15])).
% 1.62/0.59  fof(f15,axiom,(
% 1.62/0.59    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.62/0.59  fof(f161,plain,(
% 1.62/0.59    ( ! [X2,X1] : (~v1_xboole_0(k1_relat_1(X1)) | v1_xboole_0(k5_relat_1(X1,X2)) | ~v1_relat_1(k5_relat_1(X1,X2)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.62/0.59    inference(superposition,[],[f157,f52])).
% 1.62/0.59  fof(f52,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f27])).
% 1.62/0.59  fof(f27,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(flattening,[],[f26])).
% 1.62/0.59  fof(f26,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f17])).
% 1.62/0.59  fof(f17,axiom,(
% 1.62/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.62/0.59  fof(f157,plain,(
% 1.62/0.59    ( ! [X3] : (~v1_xboole_0(k1_relat_1(X3)) | v1_xboole_0(X3) | ~v1_relat_1(X3)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f152,f60])).
% 1.62/0.59  fof(f60,plain,(
% 1.62/0.59    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f31])).
% 1.62/0.59  fof(f31,plain,(
% 1.62/0.59    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f11])).
% 1.62/0.59  fof(f11,axiom,(
% 1.62/0.59    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.62/0.59  fof(f152,plain,(
% 1.62/0.59    ( ! [X3] : (v1_xboole_0(X3) | ~v1_xboole_0(k1_relat_1(X3)) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(X3),k2_relat_1(X3))) | ~v1_relat_1(X3)) )),
% 1.62/0.59    inference(superposition,[],[f60,f108])).
% 1.62/0.59  fof(f108,plain,(
% 1.62/0.59    ( ! [X1] : (k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)) = X1 | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.62/0.59    inference(superposition,[],[f80,f71])).
% 1.62/0.59  fof(f71,plain,(
% 1.62/0.59    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f50,f69])).
% 1.62/0.59  fof(f69,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.62/0.59    inference(definition_unfolding,[],[f57,f68])).
% 1.62/0.59  fof(f57,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f13])).
% 1.62/0.59  fof(f13,axiom,(
% 1.62/0.59    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.62/0.59  fof(f50,plain,(
% 1.62/0.59    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f23])).
% 1.62/0.59  fof(f23,plain,(
% 1.62/0.59    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f16])).
% 1.62/0.59  fof(f16,axiom,(
% 1.62/0.59    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 1.62/0.59  fof(f80,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) = X0 | ~v1_xboole_0(X0)) )),
% 1.62/0.59    inference(superposition,[],[f70,f53])).
% 1.62/0.59  fof(f53,plain,(
% 1.62/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f28])).
% 1.62/0.59  fof(f28,plain,(
% 1.62/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f2])).
% 1.62/0.59  fof(f2,axiom,(
% 1.62/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.62/0.59  fof(f70,plain,(
% 1.62/0.59    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.62/0.59    inference(definition_unfolding,[],[f49,f69])).
% 1.62/0.59  fof(f49,plain,(
% 1.62/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f3])).
% 1.62/0.59  fof(f3,axiom,(
% 1.62/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.62/0.59  fof(f623,plain,(
% 1.62/0.59    ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.62/0.59    inference(subsumption_resolution,[],[f616,f42])).
% 1.62/0.59  fof(f616,plain,(
% 1.62/0.59    ~v1_relat_1(sK0) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.62/0.59    inference(resolution,[],[f610,f336])).
% 1.62/0.59  fof(f336,plain,(
% 1.62/0.59    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.62/0.59    inference(subsumption_resolution,[],[f335,f48])).
% 1.62/0.59  fof(f335,plain,(
% 1.62/0.59    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.62/0.59    inference(forward_demodulation,[],[f334,f46])).
% 1.62/0.59  fof(f334,plain,(
% 1.62/0.59    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.62/0.59    inference(subsumption_resolution,[],[f333,f84])).
% 1.62/0.59  fof(f333,plain,(
% 1.62/0.59    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.62/0.59    inference(subsumption_resolution,[],[f332,f42])).
% 1.62/0.59  fof(f332,plain,(
% 1.62/0.59    ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.62/0.59    inference(subsumption_resolution,[],[f330,f45])).
% 1.62/0.59  fof(f330,plain,(
% 1.62/0.59    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.62/0.59    inference(superposition,[],[f220,f89])).
% 1.62/0.59  fof(f89,plain,(
% 1.62/0.59    ( ! [X2,X3] : (k5_relat_1(X2,X3) = k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_xboole_0(k5_relat_1(X2,X3))) )),
% 1.62/0.59    inference(superposition,[],[f52,f75])).
% 1.62/0.59  fof(f75,plain,(
% 1.62/0.59    ( ! [X0] : (k1_relat_1(X0) = X0 | ~v1_xboole_0(X0)) )),
% 1.62/0.59    inference(superposition,[],[f45,f53])).
% 1.62/0.59  fof(f220,plain,(
% 1.62/0.59    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.62/0.59    inference(subsumption_resolution,[],[f219,f48])).
% 1.62/0.59  fof(f219,plain,(
% 1.62/0.59    ~r1_tarski(k1_xboole_0,k2_relat_1(sK0)) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.62/0.59    inference(forward_demodulation,[],[f218,f45])).
% 1.62/0.59  fof(f218,plain,(
% 1.62/0.59    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0)) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.62/0.59    inference(subsumption_resolution,[],[f217,f84])).
% 1.62/0.59  fof(f217,plain,(
% 1.62/0.59    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.62/0.59    inference(subsumption_resolution,[],[f216,f42])).
% 1.62/0.59  fof(f216,plain,(
% 1.62/0.59    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.62/0.59    inference(subsumption_resolution,[],[f207,f46])).
% 1.62/0.59  fof(f207,plain,(
% 1.62/0.59    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.62/0.59    inference(superposition,[],[f43,f86])).
% 1.62/0.59  fof(f86,plain,(
% 1.62/0.59    ( ! [X2,X3] : (k5_relat_1(X2,X3) = k2_relat_1(X3) | ~r1_tarski(k1_relat_1(X3),k2_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~v1_xboole_0(k5_relat_1(X2,X3))) )),
% 1.62/0.59    inference(superposition,[],[f51,f74])).
% 1.62/0.59  fof(f74,plain,(
% 1.62/0.59    ( ! [X0] : (k2_relat_1(X0) = X0 | ~v1_xboole_0(X0)) )),
% 1.62/0.59    inference(superposition,[],[f46,f53])).
% 1.62/0.59  fof(f51,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f25])).
% 1.62/0.59  fof(f25,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(flattening,[],[f24])).
% 1.62/0.59  fof(f24,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f18])).
% 1.62/0.59  fof(f18,axiom,(
% 1.62/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 1.62/0.59  fof(f43,plain,(
% 1.62/0.59    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f36])).
% 1.62/0.59  fof(f36,plain,(
% 1.62/0.59    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f22,plain,(
% 1.62/0.59    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f21])).
% 1.62/0.59  fof(f21,negated_conjecture,(
% 1.62/0.59    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.62/0.59    inference(negated_conjecture,[],[f20])).
% 1.62/0.59  fof(f20,conjecture,(
% 1.62/0.59    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.62/0.59  fof(f610,plain,(
% 1.62/0.59    ( ! [X0] : (v1_xboole_0(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f609,f44])).
% 1.62/0.59  fof(f609,plain,(
% 1.62/0.59    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(forward_demodulation,[],[f608,f46])).
% 1.62/0.59  fof(f608,plain,(
% 1.62/0.59    ( ! [X0] : (~v1_xboole_0(k2_relat_1(k1_xboole_0)) | v1_xboole_0(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f607,f84])).
% 1.62/0.59  fof(f607,plain,(
% 1.62/0.59    ( ! [X0] : (~v1_xboole_0(k2_relat_1(k1_xboole_0)) | v1_xboole_0(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f600,f48])).
% 1.62/0.59  fof(f600,plain,(
% 1.62/0.59    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | ~v1_xboole_0(k2_relat_1(k1_xboole_0)) | v1_xboole_0(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.62/0.59    inference(superposition,[],[f328,f45])).
% 1.62/0.59  fof(f328,plain,(
% 1.62/0.59    ( ! [X8,X9] : (~r1_tarski(k1_relat_1(X9),k2_relat_1(X8)) | ~v1_xboole_0(k2_relat_1(X9)) | v1_xboole_0(k5_relat_1(X8,X9)) | ~v1_relat_1(X8) | ~v1_relat_1(X9)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f316,f59])).
% 1.62/0.59  fof(f59,plain,(
% 1.62/0.59    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f30,plain,(
% 1.62/0.59    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f10])).
% 1.62/0.59  fof(f10,axiom,(
% 1.62/0.59    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.62/0.59  fof(f316,plain,(
% 1.62/0.59    ( ! [X8,X9] : (v1_xboole_0(k5_relat_1(X8,X9)) | ~v1_xboole_0(k2_relat_1(X9)) | ~r1_tarski(k1_relat_1(X9),k2_relat_1(X8)) | ~v1_relat_1(X8) | ~v1_relat_1(X9) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(X8,X9)),k2_relat_1(X9)))) )),
% 1.62/0.59    inference(superposition,[],[f59,f131])).
% 1.62/0.59  fof(f131,plain,(
% 1.62/0.59    ( ! [X2,X3] : (k5_relat_1(X2,X3) = k2_zfmisc_1(k1_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3)) | ~r1_tarski(k1_relat_1(X3),k2_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3)))) )),
% 1.62/0.59    inference(superposition,[],[f102,f80])).
% 1.62/0.59  fof(f102,plain,(
% 1.62/0.59    ( ! [X2,X1] : (k5_relat_1(X1,X2) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))) | ~r1_tarski(k1_relat_1(X2),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2)) )),
% 1.62/0.59    inference(subsumption_resolution,[],[f96,f61])).
% 1.62/0.59  fof(f96,plain,(
% 1.62/0.59    ( ! [X2,X1] : (k5_relat_1(X1,X2) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))) | ~v1_relat_1(k5_relat_1(X1,X2)) | ~r1_tarski(k1_relat_1(X2),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2)) )),
% 1.62/0.59    inference(superposition,[],[f71,f51])).
% 1.62/0.59  fof(f42,plain,(
% 1.62/0.59    v1_relat_1(sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f36])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (9168)------------------------------
% 1.62/0.59  % (9168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (9168)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (9168)Memory used [KB]: 2174
% 1.62/0.59  % (9168)Time elapsed: 0.162 s
% 1.62/0.59  % (9168)------------------------------
% 1.62/0.59  % (9168)------------------------------
% 1.62/0.59  % (9134)Success in time 0.22 s
%------------------------------------------------------------------------------
