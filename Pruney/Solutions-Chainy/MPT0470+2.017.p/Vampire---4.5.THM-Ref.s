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
% DateTime   : Thu Dec  3 12:47:46 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  132 (2706 expanded)
%              Number of leaves         :   27 ( 869 expanded)
%              Depth                    :   34
%              Number of atoms          :  238 (3663 expanded)
%              Number of equality atoms :  112 (2747 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f655,plain,(
    $false ),
    inference(subsumption_resolution,[],[f654,f43])).

fof(f43,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f654,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f653,f366])).

fof(f366,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f345,f359])).

fof(f359,plain,(
    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f358,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f49,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f358,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f357,f192])).

fof(f192,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f160,f191])).

fof(f191,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f185,f143])).

fof(f143,plain,(
    ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1) ),
    inference(forward_demodulation,[],[f142,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f142,plain,(
    ! [X1] : k6_subset_1(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f83,f82])).

fof(f82,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f83,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f59,f79])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

% (9262)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f185,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k6_subset_1(X1,X1)) ),
    inference(superposition,[],[f143,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(definition_unfolding,[],[f69,f59,f59])).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f160,plain,(
    ! [X0,X1] : k2_zfmisc_1(X0,k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f144,f143])).

fof(f144,plain,(
    ! [X0,X1] : k2_zfmisc_1(k6_subset_1(X0,X0),X1) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f104,f143])).

fof(f104,plain,(
    ! [X0,X1] : k2_zfmisc_1(X0,k6_subset_1(X1,X1)) = k2_zfmisc_1(k6_subset_1(X0,X0),X1) ),
    inference(superposition,[],[f85,f84])).

fof(f85,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(definition_unfolding,[],[f68,f59,f59])).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f357,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) ),
    inference(forward_demodulation,[],[f348,f325])).

fof(f325,plain,(
    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f321,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f66,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f321,plain,(
    r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f319,f43])).

fof(f319,plain,
    ( r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f309,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f309,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) ),
    inference(superposition,[],[f96,f302])).

fof(f302,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    inference(resolution,[],[f287,f43])).

fof(f287,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f286,f221])).

fof(f221,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f220,f143])).

fof(f220,plain,(
    k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0)) ),
    inference(subsumption_resolution,[],[f187,f43])).

fof(f187,plain,
    ( k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f143,f123])).

fof(f123,plain,(
    ! [X7] :
      ( k4_relat_1(k6_subset_1(X7,sK0)) = k6_subset_1(k4_relat_1(X7),k4_relat_1(sK0))
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f286,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) ) ),
    inference(resolution,[],[f134,f45])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(resolution,[],[f57,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f96,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f95,f45])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f92,f51])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) ) ),
    inference(superposition,[],[f55,f46])).

fof(f46,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f348,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) ),
    inference(resolution,[],[f345,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f54,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f345,plain,(
    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f343,f43])).

fof(f343,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f337,f52])).

fof(f337,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f336,f45])).

fof(f336,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f311,f51])).

fof(f311,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(superposition,[],[f63,f302])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f653,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f651,f459])).

fof(f459,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f458])).

fof(f458,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f44,f455])).

fof(f455,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f426,f43])).

fof(f426,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f425,f80])).

fof(f425,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f424,f192])).

fof(f424,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0)))))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f423,f366])).

fof(f423,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0)))))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f419])).

fof(f419,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0)))))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f233,f97])).

fof(f97,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f96,f89])).

fof(f233,plain,(
    ! [X2,X3] :
      ( k5_relat_1(X2,X3) = k1_setfam_1(k6_enumset1(k5_relat_1(X2,X3),k5_relat_1(X2,X3),k5_relat_1(X2,X3),k5_relat_1(X2,X3),k5_relat_1(X2,X3),k5_relat_1(X2,X3),k5_relat_1(X2,X3),k2_zfmisc_1(k1_relat_1(k5_relat_1(X2,X3)),k2_relat_1(k5_relat_1(X2,X3)))))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f81,f63])).

fof(f44,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f651,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f441,f63])).

fof(f441,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f439,f221])).

fof(f439,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f53,f359])).

fof(f53,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (9251)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.49  % (9251)Refutation not found, incomplete strategy% (9251)------------------------------
% 0.21/0.49  % (9251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9251)Memory used [KB]: 10746
% 0.21/0.49  % (9251)Time elapsed: 0.088 s
% 0.21/0.49  % (9251)------------------------------
% 0.21/0.49  % (9251)------------------------------
% 0.21/0.50  % (9255)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (9259)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.50  % (9263)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (9267)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (9245)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (9242)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (9247)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (9243)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (9244)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (9268)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (9246)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (9241)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (9249)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (9253)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (9257)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (9257)Refutation not found, incomplete strategy% (9257)------------------------------
% 0.21/0.53  % (9257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9266)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.54  % (9269)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.44/0.54  % (9257)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (9257)Memory used [KB]: 10618
% 1.44/0.54  % (9257)Time elapsed: 0.130 s
% 1.44/0.54  % (9257)------------------------------
% 1.44/0.54  % (9257)------------------------------
% 1.44/0.54  % (9265)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.44/0.54  % (9269)Refutation not found, incomplete strategy% (9269)------------------------------
% 1.44/0.54  % (9269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (9269)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (9269)Memory used [KB]: 10746
% 1.44/0.54  % (9269)Time elapsed: 0.139 s
% 1.44/0.54  % (9269)------------------------------
% 1.44/0.54  % (9269)------------------------------
% 1.44/0.54  % (9261)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.44/0.54  % (9260)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.54  % (9248)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.44/0.54  % (9258)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.55  % (9252)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.55  % (9264)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.55  % (9270)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.55  % (9270)Refutation not found, incomplete strategy% (9270)------------------------------
% 1.44/0.55  % (9270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (9270)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (9270)Memory used [KB]: 1663
% 1.44/0.55  % (9270)Time elapsed: 0.145 s
% 1.44/0.55  % (9270)------------------------------
% 1.44/0.55  % (9270)------------------------------
% 1.44/0.55  % (9250)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.44/0.55  % (9256)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.54/0.56  % (9263)Refutation found. Thanks to Tanya!
% 1.54/0.56  % SZS status Theorem for theBenchmark
% 1.54/0.56  % SZS output start Proof for theBenchmark
% 1.54/0.56  fof(f655,plain,(
% 1.54/0.56    $false),
% 1.54/0.56    inference(subsumption_resolution,[],[f654,f43])).
% 1.54/0.56  fof(f43,plain,(
% 1.54/0.56    v1_relat_1(sK0)),
% 1.54/0.56    inference(cnf_transformation,[],[f40])).
% 1.54/0.56  fof(f40,plain,(
% 1.54/0.56    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f39])).
% 1.54/0.56  fof(f39,plain,(
% 1.54/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f27])).
% 1.54/0.56  fof(f27,negated_conjecture,(
% 1.54/0.56    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.54/0.56    inference(negated_conjecture,[],[f26])).
% 1.54/0.56  fof(f26,conjecture,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.54/0.56  fof(f654,plain,(
% 1.54/0.56    ~v1_relat_1(sK0)),
% 1.54/0.56    inference(subsumption_resolution,[],[f653,f366])).
% 1.54/0.56  fof(f366,plain,(
% 1.54/0.56    v1_relat_1(k1_xboole_0)),
% 1.54/0.56    inference(backward_demodulation,[],[f345,f359])).
% 1.54/0.56  fof(f359,plain,(
% 1.54/0.56    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.54/0.56    inference(forward_demodulation,[],[f358,f80])).
% 1.54/0.56  fof(f80,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f49,f79])).
% 1.54/0.56  fof(f79,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f60,f78])).
% 1.54/0.56  fof(f78,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f61,f77])).
% 1.54/0.56  fof(f77,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f67,f76])).
% 1.54/0.56  fof(f76,plain,(
% 1.54/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f70,f75])).
% 1.54/0.56  fof(f75,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f71,f74])).
% 1.54/0.56  fof(f74,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f72,f73])).
% 1.54/0.56  fof(f73,plain,(
% 1.54/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f13])).
% 1.54/0.56  fof(f13,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.54/0.56  fof(f72,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f12])).
% 1.54/0.56  fof(f12,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.54/0.56  fof(f71,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f11])).
% 1.54/0.56  fof(f11,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.54/0.56  fof(f70,plain,(
% 1.54/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f10])).
% 1.54/0.56  fof(f10,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.54/0.56  fof(f67,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f9])).
% 1.54/0.56  fof(f9,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.54/0.56  fof(f61,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f8])).
% 1.54/0.56  fof(f8,axiom,(
% 1.54/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.54/0.56  fof(f60,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f16])).
% 1.54/0.56  fof(f16,axiom,(
% 1.54/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.54/0.56  fof(f49,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f5])).
% 1.54/0.56  fof(f5,axiom,(
% 1.54/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.54/0.56  fof(f358,plain,(
% 1.54/0.56    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))),
% 1.54/0.56    inference(forward_demodulation,[],[f357,f192])).
% 1.54/0.56  fof(f192,plain,(
% 1.54/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.54/0.56    inference(backward_demodulation,[],[f160,f191])).
% 1.54/0.56  fof(f191,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f185,f143])).
% 1.54/0.56  fof(f143,plain,(
% 1.54/0.56    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f142,f50])).
% 1.54/0.56  fof(f50,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.54/0.56  fof(f142,plain,(
% 1.54/0.56    ( ! [X1] : (k6_subset_1(X1,X1) = k5_xboole_0(X1,X1)) )),
% 1.54/0.56    inference(superposition,[],[f83,f82])).
% 1.54/0.56  fof(f82,plain,(
% 1.54/0.56    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.54/0.56    inference(definition_unfolding,[],[f58,f79])).
% 1.54/0.56  fof(f58,plain,(
% 1.54/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f28])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.56    inference(rectify,[],[f2])).
% 1.54/0.56  fof(f2,axiom,(
% 1.54/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.54/0.56  fof(f83,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f62,f59,f79])).
% 1.54/0.56  fof(f59,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f15])).
% 1.54/0.56  fof(f15,axiom,(
% 1.54/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.54/0.56  % (9262)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.54/0.56  fof(f62,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f4])).
% 1.54/0.56  fof(f4,axiom,(
% 1.54/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.56  fof(f185,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k6_subset_1(X1,X1))) )),
% 1.54/0.56    inference(superposition,[],[f143,f84])).
% 1.54/0.56  fof(f84,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f69,f59,f59])).
% 1.54/0.56  fof(f69,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f14])).
% 1.54/0.56  fof(f14,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 1.54/0.56  fof(f160,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_zfmisc_1(X0,k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f144,f143])).
% 1.54/0.56  fof(f144,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_zfmisc_1(k6_subset_1(X0,X0),X1) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.54/0.56    inference(backward_demodulation,[],[f104,f143])).
% 1.54/0.56  fof(f104,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_zfmisc_1(X0,k6_subset_1(X1,X1)) = k2_zfmisc_1(k6_subset_1(X0,X0),X1)) )),
% 1.54/0.56    inference(superposition,[],[f85,f84])).
% 1.54/0.56  fof(f85,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f68,f59,f59])).
% 1.54/0.56  fof(f68,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f14])).
% 1.54/0.56  fof(f357,plain,(
% 1.54/0.56    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))))),
% 1.54/0.56    inference(forward_demodulation,[],[f348,f325])).
% 1.54/0.56  fof(f325,plain,(
% 1.54/0.56    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.54/0.56    inference(resolution,[],[f321,f89])).
% 1.54/0.56  fof(f89,plain,(
% 1.54/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.54/0.56    inference(resolution,[],[f66,f48])).
% 1.54/0.56  fof(f48,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f6])).
% 1.54/0.56  fof(f6,axiom,(
% 1.54/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.54/0.56  fof(f66,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f42,plain,(
% 1.54/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.56    inference(flattening,[],[f41])).
% 1.54/0.56  fof(f41,plain,(
% 1.54/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.56    inference(nnf_transformation,[],[f3])).
% 1.54/0.56  fof(f3,axiom,(
% 1.54/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.54/0.56  fof(f321,plain,(
% 1.54/0.56    r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0)),
% 1.54/0.56    inference(subsumption_resolution,[],[f319,f43])).
% 1.54/0.56  fof(f319,plain,(
% 1.54/0.56    r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.54/0.56    inference(resolution,[],[f309,f52])).
% 1.54/0.56  fof(f52,plain,(
% 1.54/0.56    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f31])).
% 1.54/0.56  fof(f31,plain,(
% 1.54/0.56    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f18])).
% 1.54/0.56  fof(f18,axiom,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.54/0.56  fof(f309,plain,(
% 1.54/0.56    ~v1_relat_1(k4_relat_1(sK0)) | r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0)),
% 1.54/0.56    inference(superposition,[],[f96,f302])).
% 1.54/0.56  fof(f302,plain,(
% 1.54/0.56    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),
% 1.54/0.56    inference(resolution,[],[f287,f43])).
% 1.54/0.56  fof(f287,plain,(
% 1.54/0.56    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X0))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f286,f221])).
% 1.54/0.56  fof(f221,plain,(
% 1.54/0.56    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.54/0.56    inference(forward_demodulation,[],[f220,f143])).
% 1.54/0.56  fof(f220,plain,(
% 1.54/0.56    k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0))),
% 1.54/0.56    inference(subsumption_resolution,[],[f187,f43])).
% 1.54/0.56  fof(f187,plain,(
% 1.54/0.56    k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0)) | ~v1_relat_1(sK0)),
% 1.54/0.56    inference(superposition,[],[f143,f123])).
% 1.54/0.56  fof(f123,plain,(
% 1.54/0.56    ( ! [X7] : (k4_relat_1(k6_subset_1(X7,sK0)) = k6_subset_1(k4_relat_1(X7),k4_relat_1(sK0)) | ~v1_relat_1(X7)) )),
% 1.54/0.56    inference(resolution,[],[f56,f43])).
% 1.54/0.56  fof(f56,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f35])).
% 1.54/0.56  fof(f35,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f22])).
% 1.54/0.56  fof(f22,axiom,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).
% 1.54/0.56  fof(f286,plain,(
% 1.54/0.56    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0))) )),
% 1.54/0.56    inference(resolution,[],[f134,f45])).
% 1.54/0.56  fof(f45,plain,(
% 1.54/0.56    v1_xboole_0(k1_xboole_0)),
% 1.54/0.56    inference(cnf_transformation,[],[f1])).
% 1.54/0.56  fof(f1,axiom,(
% 1.54/0.56    v1_xboole_0(k1_xboole_0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.54/0.56  fof(f134,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.54/0.56    inference(resolution,[],[f57,f51])).
% 1.54/0.56  fof(f51,plain,(
% 1.54/0.56    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f30])).
% 1.54/0.56  fof(f30,plain,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f17])).
% 1.54/0.56  fof(f17,axiom,(
% 1.54/0.56    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.54/0.56  fof(f57,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f36])).
% 1.54/0.56  fof(f36,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f24])).
% 1.54/0.56  fof(f24,axiom,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.54/0.56  fof(f96,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f95,f45])).
% 1.54/0.56  fof(f95,plain,(
% 1.54/0.56    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.54/0.56    inference(resolution,[],[f92,f51])).
% 1.54/0.56  fof(f92,plain,(
% 1.54/0.56    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)) )),
% 1.54/0.56    inference(superposition,[],[f55,f46])).
% 1.54/0.56  fof(f46,plain,(
% 1.54/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.54/0.56    inference(cnf_transformation,[],[f25])).
% 1.54/0.56  fof(f25,axiom,(
% 1.54/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.54/0.56  fof(f55,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f34])).
% 1.54/0.56  fof(f34,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f23])).
% 1.54/0.56  fof(f23,axiom,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.54/0.56  fof(f348,plain,(
% 1.54/0.56    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))))),
% 1.54/0.56    inference(resolution,[],[f345,f81])).
% 1.54/0.56  fof(f81,plain,(
% 1.54/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 1.54/0.56    inference(definition_unfolding,[],[f54,f79])).
% 1.54/0.56  fof(f54,plain,(
% 1.54/0.56    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f33])).
% 1.54/0.56  fof(f33,plain,(
% 1.54/0.56    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f21])).
% 1.54/0.56  fof(f21,axiom,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.54/0.56  fof(f345,plain,(
% 1.54/0.56    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.54/0.56    inference(subsumption_resolution,[],[f343,f43])).
% 1.54/0.56  fof(f343,plain,(
% 1.54/0.56    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~v1_relat_1(sK0)),
% 1.54/0.56    inference(resolution,[],[f337,f52])).
% 1.54/0.56  fof(f337,plain,(
% 1.54/0.56    ~v1_relat_1(k4_relat_1(sK0)) | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.54/0.56    inference(subsumption_resolution,[],[f336,f45])).
% 1.54/0.56  fof(f336,plain,(
% 1.54/0.56    ~v1_relat_1(k4_relat_1(sK0)) | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~v1_xboole_0(k1_xboole_0)),
% 1.54/0.56    inference(resolution,[],[f311,f51])).
% 1.54/0.56  fof(f311,plain,(
% 1.54/0.56    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(sK0)) | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.54/0.56    inference(superposition,[],[f63,f302])).
% 1.54/0.56  fof(f63,plain,(
% 1.54/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f38])).
% 1.54/0.56  fof(f38,plain,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(flattening,[],[f37])).
% 1.54/0.56  fof(f37,plain,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.54/0.56    inference(ennf_transformation,[],[f19])).
% 1.54/0.56  fof(f19,axiom,(
% 1.54/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.54/0.56  fof(f653,plain,(
% 1.54/0.56    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.54/0.56    inference(subsumption_resolution,[],[f651,f459])).
% 1.54/0.56  fof(f459,plain,(
% 1.54/0.56    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f458])).
% 1.54/0.56  fof(f458,plain,(
% 1.54/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.54/0.56    inference(backward_demodulation,[],[f44,f455])).
% 1.54/0.56  fof(f455,plain,(
% 1.54/0.56    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.54/0.56    inference(resolution,[],[f426,f43])).
% 1.54/0.56  fof(f426,plain,(
% 1.54/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f425,f80])).
% 1.54/0.56  fof(f425,plain,(
% 1.54/0.56    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f424,f192])).
% 1.54/0.56  fof(f424,plain,(
% 1.54/0.56    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f423,f366])).
% 1.54/0.56  fof(f423,plain,(
% 1.54/0.56    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.54/0.56    inference(duplicate_literal_removal,[],[f419])).
% 1.54/0.56  fof(f419,plain,(
% 1.54/0.56    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(superposition,[],[f233,f97])).
% 1.54/0.56  fof(f97,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(resolution,[],[f96,f89])).
% 1.54/0.56  fof(f233,plain,(
% 1.54/0.56    ( ! [X2,X3] : (k5_relat_1(X2,X3) = k1_setfam_1(k6_enumset1(k5_relat_1(X2,X3),k5_relat_1(X2,X3),k5_relat_1(X2,X3),k5_relat_1(X2,X3),k5_relat_1(X2,X3),k5_relat_1(X2,X3),k5_relat_1(X2,X3),k2_zfmisc_1(k1_relat_1(k5_relat_1(X2,X3)),k2_relat_1(k5_relat_1(X2,X3))))) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.54/0.56    inference(resolution,[],[f81,f63])).
% 1.54/0.56  fof(f44,plain,(
% 1.54/0.56    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.54/0.56    inference(cnf_transformation,[],[f40])).
% 1.54/0.56  fof(f651,plain,(
% 1.54/0.56    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.54/0.56    inference(resolution,[],[f441,f63])).
% 1.54/0.56  fof(f441,plain,(
% 1.54/0.56    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.54/0.56    inference(forward_demodulation,[],[f439,f221])).
% 1.54/0.56  fof(f439,plain,(
% 1.54/0.56    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.54/0.56    inference(superposition,[],[f53,f359])).
% 1.54/0.56  fof(f53,plain,(
% 1.54/0.56    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f32])).
% 1.54/0.56  fof(f32,plain,(
% 1.54/0.56    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f20])).
% 1.54/0.56  fof(f20,axiom,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.54/0.56  % SZS output end Proof for theBenchmark
% 1.54/0.56  % (9263)------------------------------
% 1.54/0.56  % (9263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (9263)Termination reason: Refutation
% 1.54/0.56  
% 1.54/0.56  % (9263)Memory used [KB]: 6908
% 1.54/0.56  % (9263)Time elapsed: 0.121 s
% 1.54/0.56  % (9263)------------------------------
% 1.54/0.56  % (9263)------------------------------
% 1.54/0.56  % (9240)Success in time 0.207 s
%------------------------------------------------------------------------------
