%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 906 expanded)
%              Number of leaves         :   28 ( 296 expanded)
%              Depth                    :   24
%              Number of atoms          :  276 (1269 expanded)
%              Number of equality atoms :  126 ( 926 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f49,f363,f311])).

fof(f311,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f310,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f310,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f309,f52])).

fof(f52,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f309,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f308,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f54,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f78,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f80,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f81,f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f308,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f307,f161])).

fof(f161,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f160,f132])).

fof(f132,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f95,f96])).

fof(f96,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f65,f88,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f87])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f95,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f64,f89,f90])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f69,f88])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f160,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f159,f132])).

fof(f159,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,X0),X1) ),
    inference(forward_demodulation,[],[f148,f94])).

fof(f94,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f63,f88])).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f148,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1) ),
    inference(superposition,[],[f102,f94])).

fof(f102,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) ),
    inference(definition_unfolding,[],[f76,f89,f89])).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f307,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0)))))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f301,f130])).

fof(f130,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f128,f49])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f117,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0),X1)
      | v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sK1(X1) != X0
      | v1_relat_1(X1)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f62,f60])).

fof(f60,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK2(X4),sK3(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f45,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f62,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK1(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f117,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_xboole_0),X0)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f116,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f113,f53])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f98,f110])).

fof(f110,plain,(
    ! [X0] :
      ( k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f97,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f91])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f87])).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f91])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f301,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0)))))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f123,f51])).

fof(f51,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f119,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f93,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f93,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f88])).

fof(f56,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f363,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f352,f49])).

fof(f352,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f351])).

fof(f351,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f50,f341])).

fof(f341,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f340,f53])).

fof(f340,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f339,f51])).

fof(f339,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f338,f92])).

fof(f338,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f337,f140])).

fof(f140,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f139,f132])).

fof(f139,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f138,f94])).

fof(f138,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(forward_demodulation,[],[f135,f132])).

fof(f135,plain,(
    ! [X0,X1] : k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[],[f101,f94])).

fof(f101,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) ),
    inference(definition_unfolding,[],[f77,f89,f89])).

fof(f77,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f337,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f328,f130])).

fof(f328,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)))
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f125,f52])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f121,f70])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f93,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f50,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f49,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:47:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (23784)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (23776)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (23792)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (23774)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (23769)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (23782)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (23771)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (23784)Refutation not found, incomplete strategy% (23784)------------------------------
% 0.21/0.54  % (23784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23794)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (23771)Refutation not found, incomplete strategy% (23771)------------------------------
% 0.21/0.54  % (23771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23771)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23771)Memory used [KB]: 10746
% 0.21/0.54  % (23771)Time elapsed: 0.121 s
% 0.21/0.54  % (23771)------------------------------
% 0.21/0.54  % (23771)------------------------------
% 0.21/0.54  % (23772)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (23784)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23784)Memory used [KB]: 6268
% 0.21/0.54  % (23784)Time elapsed: 0.124 s
% 0.21/0.54  % (23784)------------------------------
% 0.21/0.54  % (23784)------------------------------
% 0.21/0.54  % (23791)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (23791)Refutation not found, incomplete strategy% (23791)------------------------------
% 0.21/0.54  % (23791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23791)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23791)Memory used [KB]: 10746
% 0.21/0.54  % (23791)Time elapsed: 0.097 s
% 0.21/0.54  % (23791)------------------------------
% 0.21/0.54  % (23791)------------------------------
% 0.21/0.54  % (23773)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (23777)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (23781)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (23778)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (23775)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (23783)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (23790)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (23786)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (23785)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (23795)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (23786)Refutation not found, incomplete strategy% (23786)------------------------------
% 0.21/0.55  % (23786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23786)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23786)Memory used [KB]: 10618
% 0.21/0.55  % (23786)Time elapsed: 0.133 s
% 0.21/0.55  % (23786)------------------------------
% 0.21/0.55  % (23786)------------------------------
% 0.21/0.55  % (23788)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (23793)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (23797)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (23770)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (23798)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (23787)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (23789)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (23780)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (23779)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (23796)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (23777)Refutation not found, incomplete strategy% (23777)------------------------------
% 0.21/0.56  % (23777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (23777)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (23777)Memory used [KB]: 10746
% 0.21/0.57  % (23777)Time elapsed: 0.156 s
% 0.21/0.57  % (23777)------------------------------
% 0.21/0.57  % (23777)------------------------------
% 0.21/0.59  % (23798)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 1.82/0.61  % SZS output start Proof for theBenchmark
% 1.82/0.61  fof(f472,plain,(
% 1.82/0.61    $false),
% 1.82/0.61    inference(unit_resulting_resolution,[],[f49,f363,f311])).
% 1.82/0.61  fof(f311,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f310,f53])).
% 1.82/0.61  fof(f53,plain,(
% 1.82/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f5])).
% 1.82/0.61  fof(f5,axiom,(
% 1.82/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.82/0.61  fof(f310,plain,(
% 1.82/0.61    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f309,f52])).
% 1.82/0.61  fof(f52,plain,(
% 1.82/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.82/0.61    inference(cnf_transformation,[],[f26])).
% 1.82/0.61  fof(f26,axiom,(
% 1.82/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.82/0.61  fof(f309,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f308,f92])).
% 1.82/0.61  fof(f92,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.82/0.61    inference(definition_unfolding,[],[f54,f88])).
% 1.82/0.61  fof(f88,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.82/0.61    inference(definition_unfolding,[],[f67,f87])).
% 1.82/0.61  fof(f87,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f68,f86])).
% 1.82/0.61  fof(f86,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f75,f85])).
% 1.82/0.61  fof(f85,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f78,f84])).
% 1.82/0.61  fof(f84,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f80,f83])).
% 1.82/0.61  fof(f83,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f81,f82])).
% 1.82/0.61  fof(f82,plain,(
% 1.82/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f14])).
% 1.82/0.61  fof(f14,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.82/0.61  fof(f81,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f13])).
% 1.82/0.61  fof(f13,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.82/0.61  fof(f80,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f12])).
% 1.82/0.61  fof(f12,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.82/0.61  fof(f78,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f11])).
% 1.82/0.61  fof(f11,axiom,(
% 1.82/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.82/0.61  fof(f75,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f10])).
% 1.82/0.61  fof(f10,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.82/0.61  fof(f68,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f9])).
% 1.82/0.61  fof(f9,axiom,(
% 1.82/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.82/0.61  fof(f67,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f20])).
% 1.82/0.61  fof(f20,axiom,(
% 1.82/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.82/0.61  fof(f54,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f4])).
% 1.82/0.61  fof(f4,axiom,(
% 1.82/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.82/0.61  fof(f308,plain,(
% 1.82/0.61    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k1_xboole_0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f307,f161])).
% 1.82/0.61  fof(f161,plain,(
% 1.82/0.61    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f160,f132])).
% 1.82/0.61  fof(f132,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f95,f96])).
% 1.82/0.61  fof(f96,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0) )),
% 1.82/0.61    inference(definition_unfolding,[],[f65,f88,f90])).
% 1.82/0.61  fof(f90,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.82/0.61    inference(definition_unfolding,[],[f66,f87])).
% 1.82/0.61  fof(f66,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f16])).
% 1.82/0.61  fof(f16,axiom,(
% 1.82/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.82/0.61  fof(f65,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f3])).
% 1.82/0.61  fof(f3,axiom,(
% 1.82/0.61    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.82/0.61  fof(f95,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 1.82/0.61    inference(definition_unfolding,[],[f64,f89,f90])).
% 1.82/0.61  fof(f89,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.82/0.61    inference(definition_unfolding,[],[f69,f88])).
% 1.82/0.61  fof(f69,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f2])).
% 1.82/0.61  fof(f2,axiom,(
% 1.82/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.82/0.61  fof(f64,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f7])).
% 1.82/0.61  fof(f7,axiom,(
% 1.82/0.61    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.82/0.61  fof(f160,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f159,f132])).
% 1.82/0.61  fof(f159,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,X0),X1)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f148,f94])).
% 1.82/0.61  fof(f94,plain,(
% 1.82/0.61    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.82/0.61    inference(definition_unfolding,[],[f63,f88])).
% 1.82/0.61  fof(f63,plain,(
% 1.82/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f29])).
% 1.82/0.61  fof(f29,plain,(
% 1.82/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.82/0.61    inference(rectify,[],[f1])).
% 1.82/0.61  fof(f1,axiom,(
% 1.82/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.82/0.61  fof(f148,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1)) )),
% 1.82/0.61    inference(superposition,[],[f102,f94])).
% 1.82/0.61  fof(f102,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))) )),
% 1.82/0.61    inference(definition_unfolding,[],[f76,f89,f89])).
% 1.82/0.61  fof(f76,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f18])).
% 1.82/0.61  fof(f18,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 1.82/0.61  fof(f307,plain,(
% 1.82/0.61    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f301,f130])).
% 1.82/0.61  fof(f130,plain,(
% 1.82/0.61    v1_relat_1(k1_xboole_0)),
% 1.82/0.61    inference(resolution,[],[f128,f49])).
% 1.82/0.61  fof(f128,plain,(
% 1.82/0.61    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k1_xboole_0)) )),
% 1.82/0.61    inference(duplicate_literal_removal,[],[f126])).
% 1.82/0.61  fof(f126,plain,(
% 1.82/0.61    ( ! [X0] : (v1_relat_1(k1_xboole_0) | v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(resolution,[],[f117,f107])).
% 1.82/0.61  fof(f107,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~r2_hidden(sK1(X0),X1) | v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 1.82/0.61    inference(equality_resolution,[],[f106])).
% 1.82/0.61  fof(f106,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (sK1(X1) != X0 | v1_relat_1(X1) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 1.82/0.61    inference(superposition,[],[f62,f60])).
% 1.82/0.61  fof(f60,plain,(
% 1.82/0.61    ( ! [X4,X0] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f46])).
% 1.82/0.61  fof(f46,plain,(
% 1.82/0.61    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.82/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f45,f44])).
% 1.82/0.61  fof(f44,plain,(
% 1.82/0.61    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.82/0.61    introduced(choice_axiom,[])).
% 1.82/0.61  fof(f45,plain,(
% 1.82/0.61    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 1.82/0.61    introduced(choice_axiom,[])).
% 1.82/0.61  fof(f43,plain,(
% 1.82/0.61    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.82/0.61    inference(rectify,[],[f42])).
% 1.82/0.61  fof(f42,plain,(
% 1.82/0.61    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.82/0.61    inference(nnf_transformation,[],[f37])).
% 1.82/0.61  fof(f37,plain,(
% 1.82/0.61    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.82/0.61    inference(ennf_transformation,[],[f21])).
% 1.82/0.61  fof(f21,axiom,(
% 1.82/0.61    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.82/0.61  fof(f62,plain,(
% 1.82/0.61    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK1(X0) | v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f46])).
% 1.82/0.61  fof(f117,plain,(
% 1.82/0.61    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0),X0) | v1_relat_1(k1_xboole_0)) )),
% 1.82/0.61    inference(resolution,[],[f116,f61])).
% 1.82/0.61  fof(f61,plain,(
% 1.82/0.61    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f46])).
% 1.82/0.61  fof(f116,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f113,f53])).
% 1.82/0.61  fof(f113,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.82/0.61    inference(superposition,[],[f98,f110])).
% 1.82/0.61  fof(f110,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.82/0.61    inference(resolution,[],[f97,f59])).
% 1.82/0.61  fof(f59,plain,(
% 1.82/0.61    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f36])).
% 1.82/0.61  fof(f36,plain,(
% 1.82/0.61    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.82/0.61    inference(ennf_transformation,[],[f6])).
% 1.82/0.61  fof(f6,axiom,(
% 1.82/0.61    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.82/0.61  fof(f97,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f72,f91])).
% 1.82/0.61  fof(f91,plain,(
% 1.82/0.61    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f55,f87])).
% 1.82/0.61  fof(f55,plain,(
% 1.82/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f8])).
% 1.82/0.61  fof(f8,axiom,(
% 1.82/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.82/0.61  fof(f72,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f47])).
% 1.82/0.61  fof(f47,plain,(
% 1.82/0.61    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.82/0.61    inference(nnf_transformation,[],[f15])).
% 1.82/0.61  fof(f15,axiom,(
% 1.82/0.61    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.82/0.61  fof(f98,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f71,f91])).
% 1.82/0.61  fof(f71,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f47])).
% 1.82/0.61  fof(f301,plain,(
% 1.82/0.61    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.82/0.61    inference(superposition,[],[f123,f51])).
% 1.82/0.61  fof(f51,plain,(
% 1.82/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.82/0.61    inference(cnf_transformation,[],[f26])).
% 1.82/0.61  fof(f123,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f119,f70])).
% 1.82/0.61  fof(f70,plain,(
% 1.82/0.61    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f39])).
% 1.82/0.61  fof(f39,plain,(
% 1.82/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.82/0.61    inference(flattening,[],[f38])).
% 1.82/0.61  fof(f38,plain,(
% 1.82/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.82/0.61    inference(ennf_transformation,[],[f22])).
% 1.82/0.61  fof(f22,axiom,(
% 1.82/0.61    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.82/0.61  fof(f119,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(superposition,[],[f93,f58])).
% 1.82/0.61  fof(f58,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f35])).
% 1.82/0.61  fof(f35,plain,(
% 1.82/0.61    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.82/0.61    inference(flattening,[],[f34])).
% 1.82/0.61  fof(f34,plain,(
% 1.82/0.61    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.82/0.61    inference(ennf_transformation,[],[f24])).
% 1.82/0.61  fof(f24,axiom,(
% 1.82/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.82/0.61  fof(f93,plain,(
% 1.82/0.61    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(definition_unfolding,[],[f56,f88])).
% 1.82/0.61  fof(f56,plain,(
% 1.82/0.61    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f31])).
% 1.82/0.61  fof(f31,plain,(
% 1.82/0.61    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.82/0.61    inference(ennf_transformation,[],[f23])).
% 1.82/0.61  fof(f23,axiom,(
% 1.82/0.61    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 1.82/0.61  fof(f363,plain,(
% 1.82/0.61    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.82/0.61    inference(subsumption_resolution,[],[f352,f49])).
% 1.82/0.61  fof(f352,plain,(
% 1.82/0.61    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(sK0)),
% 1.82/0.61    inference(trivial_inequality_removal,[],[f351])).
% 1.82/0.61  fof(f351,plain,(
% 1.82/0.61    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(sK0)),
% 1.82/0.61    inference(superposition,[],[f50,f341])).
% 1.82/0.61  fof(f341,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f340,f53])).
% 1.82/0.61  fof(f340,plain,(
% 1.82/0.61    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f339,f51])).
% 1.82/0.61  fof(f339,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f338,f92])).
% 1.82/0.61  fof(f338,plain,(
% 1.82/0.61    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k1_xboole_0)) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f337,f140])).
% 1.82/0.61  fof(f140,plain,(
% 1.82/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.82/0.61    inference(forward_demodulation,[],[f139,f132])).
% 1.82/0.61  fof(f139,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,X1))) )),
% 1.82/0.61    inference(forward_demodulation,[],[f138,f94])).
% 1.82/0.61  fof(f138,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.82/0.61    inference(forward_demodulation,[],[f135,f132])).
% 1.82/0.61  fof(f135,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1))) )),
% 1.82/0.61    inference(superposition,[],[f101,f94])).
% 1.82/0.61  fof(f101,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))))) )),
% 1.82/0.61    inference(definition_unfolding,[],[f77,f89,f89])).
% 1.82/0.61  fof(f77,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f18])).
% 1.82/0.61  fof(f337,plain,(
% 1.82/0.61    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0))) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f328,f130])).
% 1.82/0.61  fof(f328,plain,(
% 1.82/0.61    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0))) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.82/0.61    inference(superposition,[],[f125,f52])).
% 1.82/0.61  fof(f125,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)))) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 1.82/0.61    inference(subsumption_resolution,[],[f121,f70])).
% 1.82/0.61  fof(f121,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 1.82/0.61    inference(superposition,[],[f93,f57])).
% 1.82/0.61  fof(f57,plain,(
% 1.82/0.61    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f33])).
% 1.82/0.61  fof(f33,plain,(
% 1.82/0.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.82/0.61    inference(flattening,[],[f32])).
% 1.82/0.61  fof(f32,plain,(
% 1.82/0.61    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.82/0.61    inference(ennf_transformation,[],[f25])).
% 1.82/0.61  fof(f25,axiom,(
% 1.82/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 1.82/0.61  fof(f50,plain,(
% 1.82/0.61    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.82/0.61    inference(cnf_transformation,[],[f41])).
% 1.82/0.61  fof(f41,plain,(
% 1.82/0.61    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.82/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f40])).
% 1.82/0.61  fof(f40,plain,(
% 1.82/0.61    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.82/0.61    introduced(choice_axiom,[])).
% 1.82/0.61  fof(f30,plain,(
% 1.82/0.61    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.82/0.61    inference(ennf_transformation,[],[f28])).
% 1.82/0.61  fof(f28,negated_conjecture,(
% 1.82/0.61    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.82/0.61    inference(negated_conjecture,[],[f27])).
% 1.82/0.61  fof(f27,conjecture,(
% 1.82/0.61    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.82/0.61  fof(f49,plain,(
% 1.82/0.61    v1_relat_1(sK0)),
% 1.82/0.61    inference(cnf_transformation,[],[f41])).
% 1.82/0.61  % SZS output end Proof for theBenchmark
% 1.82/0.61  % (23798)------------------------------
% 1.82/0.61  % (23798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (23798)Termination reason: Refutation
% 1.82/0.61  
% 1.82/0.61  % (23798)Memory used [KB]: 2174
% 1.82/0.61  % (23798)Time elapsed: 0.188 s
% 1.82/0.61  % (23798)------------------------------
% 1.82/0.61  % (23798)------------------------------
% 1.82/0.61  % (23768)Success in time 0.246 s
%------------------------------------------------------------------------------
