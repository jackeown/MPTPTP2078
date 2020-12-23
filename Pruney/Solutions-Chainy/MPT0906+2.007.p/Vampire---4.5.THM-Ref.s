%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 340 expanded)
%              Number of leaves         :   17 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  138 ( 509 expanded)
%              Number of equality atoms :  122 ( 458 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f79,f97])).

fof(f97,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f96,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f96,plain,(
    ! [X2,X0] : k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(X0,X0),X2) ),
    inference(forward_demodulation,[],[f89,f25])).

fof(f89,plain,(
    ! [X2,X0] : k2_zfmisc_1(k5_xboole_0(X0,X0),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2)) ),
    inference(superposition,[],[f56,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f26,f47,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f46])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) ),
    inference(backward_demodulation,[],[f52,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) ),
    inference(definition_unfolding,[],[f36,f47,f47])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) ),
    inference(definition_unfolding,[],[f34,f48,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f47])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f79,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f22,f78])).

fof(f78,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f65,f72])).

fof(f72,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f71,f25])).

fof(f71,plain,(
    ! [X2,X0] : k1_xboole_0 = k2_zfmisc_1(X2,k5_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f70,f25])).

fof(f70,plain,(
    ! [X2,X0] : k2_zfmisc_1(X2,k5_xboole_0(X0,X0)) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0)) ),
    inference(superposition,[],[f55,f50])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(backward_demodulation,[],[f51,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f37,f47,f47])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) ),
    inference(definition_unfolding,[],[f35,f48,f48])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f22,f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f61,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1) )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( k2_mcart_1(X2) = X2
          | k1_mcart_1(X2) = X2 )
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
       => ! [X2] :
            ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
           => ( k2_mcart_1(X2) != X2
              & k1_mcart_1(X2) != X2 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sK2 != sK2
      | ~ m1_subset_1(sK2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f31,f59])).

fof(f59,plain,
    ( sK2 = k1_mcart_1(sK2)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,
    ( sK2 != sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK2 = k1_mcart_1(sK2) ),
    inference(superposition,[],[f57,f24])).

fof(f24,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,
    ( sK2 != k2_mcart_1(sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f32,f23])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_mcart_1(X2) != X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:08:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (7260)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (7272)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (7271)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (7260)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f104])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0),
% 0.22/0.48    inference(superposition,[],[f79,f97])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f96,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X2,X0] : (k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(X0,X0),X2)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f89,f25])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X2,X0] : (k2_zfmisc_1(k5_xboole_0(X0,X0),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2))) )),
% 0.22/0.48    inference(superposition,[],[f56,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0) )),
% 0.22/0.48    inference(definition_unfolding,[],[f26,f47,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f27,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f29,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f33,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f38,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f39,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f40,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f28,f46])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f52,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f36,f47,f47])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f34,f48,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f30,f47])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.22/0.48    inference(backward_demodulation,[],[f22,f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    k1_xboole_0 = sK0),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.22/0.48    inference(superposition,[],[f65,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f71,f25])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X2,X0] : (k1_xboole_0 = k2_zfmisc_1(X2,k5_xboole_0(X0,X0))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f70,f25])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X2,X0] : (k2_zfmisc_1(X2,k5_xboole_0(X0,X0)) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0))) )),
% 0.22/0.48    inference(superposition,[],[f55,f50])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f51,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f37,f47,f47])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f35,f48,f48])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.22/0.48    inference(superposition,[],[f22,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.22/0.48    inference(resolution,[],[f61,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) => (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != k2_zfmisc_1(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.22/0.48    inference(negated_conjecture,[],[f15])).
% 0.22/0.48  fof(f15,conjecture,(
% 0.22/0.48    ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sK2 != sK2 | ~m1_subset_1(sK2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 0.22/0.48    inference(superposition,[],[f31,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    sK2 = k1_mcart_1(sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    sK2 != sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK2 = k1_mcart_1(sK2)),
% 0.22/0.48    inference(superposition,[],[f57,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    sK2 != k2_mcart_1(sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.48    inference(resolution,[],[f32,f23])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_mcart_1(X2) != X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (7260)------------------------------
% 0.22/0.48  % (7260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7260)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (7260)Memory used [KB]: 1663
% 0.22/0.48  % (7260)Time elapsed: 0.063 s
% 0.22/0.48  % (7260)------------------------------
% 0.22/0.48  % (7260)------------------------------
% 0.22/0.48  % (7261)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (7258)Success in time 0.116 s
%------------------------------------------------------------------------------
