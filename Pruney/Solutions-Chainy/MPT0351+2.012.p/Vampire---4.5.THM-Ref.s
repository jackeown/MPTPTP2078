%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:04 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 508 expanded)
%              Number of leaves         :   17 ( 167 expanded)
%              Depth                    :   18
%              Number of atoms          :  134 ( 615 expanded)
%              Number of equality atoms :   76 ( 457 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f602,plain,(
    $false ),
    inference(subsumption_resolution,[],[f601,f58])).

fof(f58,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f29,f30])).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f29,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f601,plain,(
    sK0 = k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f600,f399])).

fof(f399,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f71,f381])).

fof(f381,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f75,f379])).

fof(f379,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f365,f343])).

fof(f343,plain,(
    ! [X6] : k1_xboole_0 = k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(X6,X6))) ),
    inference(superposition,[],[f60,f75])).

fof(f60,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f55,f52])).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f37,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f55,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f42,f48,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f365,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))) ),
    inference(superposition,[],[f348,f75])).

fof(f348,plain,(
    ! [X7] : k3_tarski(k1_enumset1(X7,X7,k4_xboole_0(k1_xboole_0,X7))) = X7 ),
    inference(forward_demodulation,[],[f347,f52])).

fof(f347,plain,(
    ! [X7] : k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,X7),k4_xboole_0(k1_xboole_0,X7),X7)) = X7 ),
    inference(forward_demodulation,[],[f330,f161])).

fof(f161,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(backward_demodulation,[],[f89,f152])).

fof(f152,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f149,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f149,plain,(
    ! [X4] : k5_xboole_0(k1_xboole_0,X4) = X4 ),
    inference(forward_demodulation,[],[f145,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f145,plain,(
    ! [X4] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X4,k1_xboole_0)) = X4 ),
    inference(superposition,[],[f54,f64])).

fof(f64,plain,(
    ! [X0] : k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f50,f52])).

fof(f50,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f31,f48])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f89,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(superposition,[],[f69,f75])).

fof(f69,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(resolution,[],[f56,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f330,plain,(
    ! [X7] : k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,X7),k4_xboole_0(k1_xboole_0,X7),k4_xboole_0(X7,k4_xboole_0(k1_xboole_0,X7)))) = X7 ),
    inference(superposition,[],[f60,f151])).

fof(f151,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f149,f94])).

fof(f94,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2)) ),
    inference(superposition,[],[f49,f75])).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f53,f32])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f41,f41])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f49,f32])).

fof(f600,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f596,f523])).

fof(f523,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f515,f400])).

fof(f400,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f73,f381])).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f49,f69])).

fof(f515,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f49,f508])).

fof(f508,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f507,f56])).

fof(f507,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f505])).

fof(f505,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f503,f46])).

fof(f503,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f68,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(sK2(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f44,f45])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f596,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f592,f457])).

fof(f457,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f141,f54])).

fof(f141,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[],[f54,f52])).

fof(f592,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f567,f28])).

fof(f567,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X2,X1,X2) ) ),
    inference(resolution,[],[f61,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f33,f30])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    inference(forward_demodulation,[],[f57,f54])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:42:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (15824)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (15832)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (15832)Refutation not found, incomplete strategy% (15832)------------------------------
% 0.22/0.52  % (15832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15844)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (15832)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15832)Memory used [KB]: 10618
% 0.22/0.52  % (15832)Time elapsed: 0.114 s
% 0.22/0.52  % (15832)------------------------------
% 0.22/0.52  % (15832)------------------------------
% 0.22/0.53  % (15823)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (15823)Refutation not found, incomplete strategy% (15823)------------------------------
% 0.22/0.53  % (15823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15823)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15823)Memory used [KB]: 1663
% 0.22/0.53  % (15823)Time elapsed: 0.113 s
% 0.22/0.53  % (15823)------------------------------
% 0.22/0.53  % (15823)------------------------------
% 0.22/0.53  % (15829)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (15844)Refutation not found, incomplete strategy% (15844)------------------------------
% 0.22/0.53  % (15844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15844)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15844)Memory used [KB]: 1663
% 0.22/0.53  % (15844)Time elapsed: 0.117 s
% 0.22/0.53  % (15844)------------------------------
% 0.22/0.53  % (15844)------------------------------
% 0.22/0.53  % (15837)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (15851)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (15838)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (15850)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (15828)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (15826)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.54  % (15843)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.54  % (15846)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.54  % (15831)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.54  % (15843)Refutation not found, incomplete strategy% (15843)------------------------------
% 1.41/0.54  % (15843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (15843)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (15843)Memory used [KB]: 10746
% 1.41/0.54  % (15843)Time elapsed: 0.127 s
% 1.41/0.54  % (15843)------------------------------
% 1.41/0.54  % (15843)------------------------------
% 1.41/0.55  % (15842)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (15834)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (15834)Refutation not found, incomplete strategy% (15834)------------------------------
% 1.41/0.55  % (15834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (15834)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (15834)Memory used [KB]: 10746
% 1.41/0.55  % (15834)Time elapsed: 0.139 s
% 1.41/0.55  % (15834)------------------------------
% 1.41/0.55  % (15834)------------------------------
% 1.41/0.55  % (15830)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (15849)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.55  % (15852)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (15847)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.55  % (15849)Refutation not found, incomplete strategy% (15849)------------------------------
% 1.41/0.55  % (15849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (15849)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (15849)Memory used [KB]: 10746
% 1.41/0.55  % (15849)Time elapsed: 0.150 s
% 1.41/0.55  % (15849)------------------------------
% 1.41/0.55  % (15849)------------------------------
% 1.41/0.55  % (15845)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.55  % (15833)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (15839)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (15836)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (15833)Refutation not found, incomplete strategy% (15833)------------------------------
% 1.41/0.55  % (15833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (15840)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.56  % (15848)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.56  % (15829)Refutation found. Thanks to Tanya!
% 1.41/0.56  % SZS status Theorem for theBenchmark
% 1.54/0.56  % (15840)Refutation not found, incomplete strategy% (15840)------------------------------
% 1.54/0.56  % (15840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (15831)Refutation not found, incomplete strategy% (15831)------------------------------
% 1.54/0.56  % (15831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (15831)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (15831)Memory used [KB]: 10746
% 1.54/0.56  % (15831)Time elapsed: 0.140 s
% 1.54/0.56  % (15831)------------------------------
% 1.54/0.56  % (15831)------------------------------
% 1.54/0.56  % (15848)Refutation not found, incomplete strategy% (15848)------------------------------
% 1.54/0.56  % (15848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (15840)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (15840)Memory used [KB]: 10618
% 1.54/0.56  % (15840)Time elapsed: 0.150 s
% 1.54/0.56  % (15840)------------------------------
% 1.54/0.56  % (15840)------------------------------
% 1.54/0.56  % (15825)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.54/0.56  % (15827)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.54/0.57  % (15835)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.57  % (15848)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (15848)Memory used [KB]: 6396
% 1.54/0.57  % (15848)Time elapsed: 0.151 s
% 1.54/0.57  % (15848)------------------------------
% 1.54/0.57  % (15848)------------------------------
% 1.54/0.57  % (15833)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (15833)Memory used [KB]: 10618
% 1.54/0.57  % (15833)Time elapsed: 0.147 s
% 1.54/0.57  % (15833)------------------------------
% 1.54/0.57  % (15833)------------------------------
% 1.54/0.58  % (15825)Refutation not found, incomplete strategy% (15825)------------------------------
% 1.54/0.58  % (15825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (15825)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (15825)Memory used [KB]: 10746
% 1.54/0.58  % (15825)Time elapsed: 0.163 s
% 1.54/0.58  % (15825)------------------------------
% 1.54/0.58  % (15825)------------------------------
% 1.54/0.58  % SZS output start Proof for theBenchmark
% 1.54/0.58  fof(f602,plain,(
% 1.54/0.58    $false),
% 1.54/0.58    inference(subsumption_resolution,[],[f601,f58])).
% 1.54/0.58  fof(f58,plain,(
% 1.54/0.58    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 1.54/0.58    inference(backward_demodulation,[],[f29,f30])).
% 1.54/0.58  fof(f30,plain,(
% 1.54/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f14])).
% 1.54/0.58  fof(f14,axiom,(
% 1.54/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.54/0.58  fof(f29,plain,(
% 1.54/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.54/0.58    inference(cnf_transformation,[],[f22])).
% 1.54/0.58  fof(f22,plain,(
% 1.54/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f19])).
% 1.54/0.58  fof(f19,negated_conjecture,(
% 1.54/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.54/0.58    inference(negated_conjecture,[],[f18])).
% 1.54/0.58  fof(f18,conjecture,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 1.54/0.58  fof(f601,plain,(
% 1.54/0.58    sK0 = k4_subset_1(sK0,sK1,sK0)),
% 1.54/0.58    inference(forward_demodulation,[],[f600,f399])).
% 1.54/0.58  fof(f399,plain,(
% 1.54/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.58    inference(backward_demodulation,[],[f71,f381])).
% 1.54/0.58  fof(f381,plain,(
% 1.54/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.54/0.58    inference(backward_demodulation,[],[f75,f379])).
% 1.54/0.58  fof(f379,plain,(
% 1.54/0.58    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f365,f343])).
% 1.54/0.58  fof(f343,plain,(
% 1.54/0.58    ( ! [X6] : (k1_xboole_0 = k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(X6,X6)))) )),
% 1.54/0.58    inference(superposition,[],[f60,f75])).
% 1.54/0.58  fof(f60,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 1.54/0.58    inference(forward_demodulation,[],[f55,f52])).
% 1.54/0.58  fof(f52,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.54/0.58    inference(definition_unfolding,[],[f35,f37,f37])).
% 1.54/0.58  fof(f37,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f12])).
% 1.54/0.58  fof(f12,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.54/0.58  fof(f35,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f11])).
% 1.54/0.58  fof(f11,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.54/0.58  fof(f55,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 1.54/0.58    inference(definition_unfolding,[],[f42,f48,f41])).
% 1.54/0.58  fof(f41,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f8])).
% 1.54/0.58  fof(f8,axiom,(
% 1.54/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.54/0.58  fof(f48,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.54/0.58    inference(definition_unfolding,[],[f38,f37])).
% 1.54/0.58  fof(f38,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f13])).
% 1.54/0.58  fof(f13,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.54/0.58  fof(f42,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f9])).
% 1.54/0.58  fof(f9,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.54/0.58  fof(f365,plain,(
% 1.54/0.58    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)))) )),
% 1.54/0.58    inference(superposition,[],[f348,f75])).
% 1.54/0.58  fof(f348,plain,(
% 1.54/0.58    ( ! [X7] : (k3_tarski(k1_enumset1(X7,X7,k4_xboole_0(k1_xboole_0,X7))) = X7) )),
% 1.54/0.58    inference(forward_demodulation,[],[f347,f52])).
% 1.54/0.58  fof(f347,plain,(
% 1.54/0.58    ( ! [X7] : (k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,X7),k4_xboole_0(k1_xboole_0,X7),X7)) = X7) )),
% 1.54/0.58    inference(forward_demodulation,[],[f330,f161])).
% 1.54/0.58  fof(f161,plain,(
% 1.54/0.58    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1) )),
% 1.54/0.58    inference(backward_demodulation,[],[f89,f152])).
% 1.54/0.58  fof(f152,plain,(
% 1.54/0.58    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 1.54/0.58    inference(superposition,[],[f149,f49])).
% 1.54/0.58  fof(f49,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.54/0.58    inference(definition_unfolding,[],[f39,f41])).
% 1.54/0.58  fof(f39,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f4])).
% 1.54/0.58  fof(f4,axiom,(
% 1.54/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.58  fof(f149,plain,(
% 1.54/0.58    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = X4) )),
% 1.54/0.58    inference(forward_demodulation,[],[f145,f32])).
% 1.54/0.58  fof(f32,plain,(
% 1.54/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f7])).
% 1.54/0.58  fof(f7,axiom,(
% 1.54/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.54/0.58  fof(f145,plain,(
% 1.54/0.58    ( ! [X4] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X4,k1_xboole_0)) = X4) )),
% 1.54/0.58    inference(superposition,[],[f54,f64])).
% 1.54/0.58  fof(f64,plain,(
% 1.54/0.58    ( ! [X0] : (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.54/0.58    inference(superposition,[],[f50,f52])).
% 1.54/0.58  fof(f50,plain,(
% 1.54/0.58    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 1.54/0.58    inference(definition_unfolding,[],[f31,f48])).
% 1.54/0.58  fof(f31,plain,(
% 1.54/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f5])).
% 1.54/0.58  fof(f5,axiom,(
% 1.54/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.54/0.58  fof(f54,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.54/0.58    inference(definition_unfolding,[],[f40,f48])).
% 1.54/0.58  fof(f40,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f10])).
% 1.54/0.58  fof(f10,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.54/0.58  fof(f89,plain,(
% 1.54/0.58    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = X1) )),
% 1.54/0.58    inference(superposition,[],[f69,f75])).
% 1.54/0.58  fof(f69,plain,(
% 1.54/0.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.54/0.58    inference(resolution,[],[f56,f63])).
% 1.54/0.58  fof(f63,plain,(
% 1.54/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.54/0.58    inference(duplicate_literal_removal,[],[f62])).
% 1.54/0.58  fof(f62,plain,(
% 1.54/0.58    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.54/0.58    inference(resolution,[],[f46,f45])).
% 1.54/0.58  fof(f45,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f25])).
% 1.54/0.58  fof(f25,plain,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f21])).
% 1.54/0.58  fof(f21,plain,(
% 1.54/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.54/0.58    inference(unused_predicate_definition_removal,[],[f2])).
% 1.54/0.58  fof(f2,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.54/0.58  fof(f46,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f25])).
% 1.54/0.58  fof(f56,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.54/0.58    inference(definition_unfolding,[],[f43,f41])).
% 1.54/0.58  fof(f43,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f23])).
% 1.54/0.58  fof(f23,plain,(
% 1.54/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.54/0.58    inference(ennf_transformation,[],[f6])).
% 1.54/0.58  fof(f6,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.54/0.58  fof(f330,plain,(
% 1.54/0.58    ( ! [X7] : (k3_tarski(k1_enumset1(k4_xboole_0(k1_xboole_0,X7),k4_xboole_0(k1_xboole_0,X7),k4_xboole_0(X7,k4_xboole_0(k1_xboole_0,X7)))) = X7) )),
% 1.54/0.58    inference(superposition,[],[f60,f151])).
% 1.54/0.58  fof(f151,plain,(
% 1.54/0.58    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 1.54/0.58    inference(superposition,[],[f149,f94])).
% 1.54/0.58  fof(f94,plain,(
% 1.54/0.58    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2))) )),
% 1.54/0.58    inference(superposition,[],[f49,f75])).
% 1.54/0.58  fof(f75,plain,(
% 1.54/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.54/0.58    inference(superposition,[],[f53,f32])).
% 1.54/0.58  fof(f53,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.54/0.58    inference(definition_unfolding,[],[f36,f41,f41])).
% 1.54/0.58  fof(f36,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f1])).
% 1.54/0.58  fof(f1,axiom,(
% 1.54/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.58  fof(f71,plain,(
% 1.54/0.58    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.54/0.58    inference(superposition,[],[f49,f32])).
% 1.54/0.58  fof(f600,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.54/0.58    inference(forward_demodulation,[],[f596,f523])).
% 1.54/0.58  fof(f523,plain,(
% 1.54/0.58    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.54/0.58    inference(forward_demodulation,[],[f515,f400])).
% 1.54/0.58  fof(f400,plain,(
% 1.54/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.54/0.58    inference(backward_demodulation,[],[f73,f381])).
% 1.54/0.58  fof(f73,plain,(
% 1.54/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.54/0.58    inference(superposition,[],[f49,f69])).
% 1.54/0.58  fof(f515,plain,(
% 1.54/0.58    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 1.54/0.58    inference(superposition,[],[f49,f508])).
% 1.54/0.58  fof(f508,plain,(
% 1.54/0.58    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 1.54/0.58    inference(resolution,[],[f507,f56])).
% 1.54/0.58  fof(f507,plain,(
% 1.54/0.58    r1_tarski(sK1,sK0)),
% 1.54/0.58    inference(duplicate_literal_removal,[],[f505])).
% 1.54/0.58  fof(f505,plain,(
% 1.54/0.58    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 1.54/0.58    inference(resolution,[],[f503,f46])).
% 1.54/0.58  fof(f503,plain,(
% 1.54/0.58    ( ! [X0] : (r2_hidden(sK2(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 1.54/0.58    inference(resolution,[],[f68,f28])).
% 1.54/0.58  fof(f28,plain,(
% 1.54/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(cnf_transformation,[],[f22])).
% 1.54/0.58  fof(f68,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(sK2(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 1.54/0.58    inference(resolution,[],[f44,f45])).
% 1.54/0.58  fof(f44,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f24])).
% 1.54/0.58  fof(f24,plain,(
% 1.54/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f16])).
% 1.54/0.58  fof(f16,axiom,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.54/0.58  fof(f596,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 1.54/0.58    inference(superposition,[],[f592,f457])).
% 1.54/0.58  fof(f457,plain,(
% 1.54/0.58    ( ! [X4,X3] : (k5_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 1.54/0.58    inference(superposition,[],[f141,f54])).
% 1.54/0.58  fof(f141,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X1,X1,X0))) )),
% 1.54/0.58    inference(superposition,[],[f54,f52])).
% 1.54/0.58  fof(f592,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(resolution,[],[f567,f28])).
% 1.54/0.58  fof(f567,plain,(
% 1.54/0.58    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X2,X1,X2)) )),
% 1.54/0.58    inference(resolution,[],[f61,f59])).
% 1.54/0.58  fof(f59,plain,(
% 1.54/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(forward_demodulation,[],[f33,f30])).
% 1.54/0.58  fof(f33,plain,(
% 1.54/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f15])).
% 1.54/0.58  fof(f15,axiom,(
% 1.54/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.54/0.58  fof(f61,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 1.54/0.58    inference(forward_demodulation,[],[f57,f54])).
% 1.54/0.58  fof(f57,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 1.54/0.58    inference(definition_unfolding,[],[f47,f48])).
% 1.54/0.58  fof(f47,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f27])).
% 1.54/0.58  fof(f27,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(flattening,[],[f26])).
% 1.54/0.58  fof(f26,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.54/0.58    inference(ennf_transformation,[],[f17])).
% 1.54/0.58  fof(f17,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.54/0.58  % SZS output end Proof for theBenchmark
% 1.54/0.58  % (15829)------------------------------
% 1.54/0.58  % (15829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (15829)Termination reason: Refutation
% 1.54/0.58  
% 1.54/0.58  % (15829)Memory used [KB]: 6524
% 1.54/0.58  % (15829)Time elapsed: 0.123 s
% 1.54/0.58  % (15829)------------------------------
% 1.54/0.58  % (15829)------------------------------
% 1.54/0.58  % (15822)Success in time 0.215 s
%------------------------------------------------------------------------------
