%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:23 EST 2020

% Result     : Theorem 5.55s
% Output     : Refutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 233 expanded)
%              Number of leaves         :   15 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 410 expanded)
%              Number of equality atoms :   62 ( 181 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5233,plain,(
    $false ),
    inference(global_subsumption,[],[f2795,f5232])).

fof(f5232,plain,(
    ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f5179])).

fof(f5179,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f443,f5178])).

fof(f5178,plain,(
    ! [X56] : k4_xboole_0(sK0,k4_xboole_0(X56,sK2)) = k2_xboole_0(sK2,k4_xboole_0(sK0,X56)) ),
    inference(forward_demodulation,[],[f5078,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f5078,plain,(
    ! [X56] : k4_xboole_0(sK0,k4_xboole_0(X56,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X56),sK2) ),
    inference(superposition,[],[f3192,f123])).

fof(f123,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f122,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f122,plain,(
    r1_tarski(sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f64,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),sK0)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f57,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f3192,plain,(
    ! [X6,X4,X5] : k2_xboole_0(k4_xboole_0(X4,X6),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = k4_xboole_0(X4,k4_xboole_0(X6,X5)) ),
    inference(backward_demodulation,[],[f288,f3186])).

fof(f3186,plain,(
    ! [X41,X42,X40] : k4_xboole_0(X40,k4_xboole_0(X41,X42)) = k4_xboole_0(X40,k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X40,X42)))) ),
    inference(global_subsumption,[],[f53,f3185])).

fof(f3185,plain,(
    ! [X41,X42,X40] :
      ( k4_xboole_0(X40,k4_xboole_0(X41,X42)) = k4_xboole_0(X40,k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X40,X42))))
      | ~ r1_tarski(X40,X40) ) ),
    inference(forward_demodulation,[],[f2990,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f41,f33,f33])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f2990,plain,(
    ! [X41,X42,X40] :
      ( k4_xboole_0(X40,k4_xboole_0(X41,X42)) = k4_xboole_0(X40,k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,X40)),X42))
      | ~ r1_tarski(X40,X40) ) ),
    inference(superposition,[],[f234,f232])).

fof(f232,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6))) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X6) ),
    inference(superposition,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f234,plain,(
    ! [X12,X10,X11] :
      ( k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,X12))) = k4_xboole_0(X10,X12)
      | ~ r1_tarski(X10,X11) ) ),
    inference(superposition,[],[f49,f48])).

fof(f53,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f40,f39])).

fof(f288,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X4,X5)))) = k2_xboole_0(k4_xboole_0(X4,X6),k4_xboole_0(X5,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f50,f47])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f42,f33])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f443,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f171,f441])).

fof(f441,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f425,f31])).

fof(f425,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f93,f28,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f93,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f56,f72])).

fof(f72,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f171,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f169,f166])).

fof(f166,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0) ),
    inference(unit_resulting_resolution,[],[f30,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f169,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f107,f166])).

fof(f107,plain,
    ( k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2)
    | ~ m1_subset_1(k7_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f77,f72])).

fof(f77,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) != k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2))
    | ~ m1_subset_1(k7_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f29,f36])).

fof(f29,plain,(
    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f2795,plain,(
    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f125,f1708])).

fof(f1708,plain,(
    k4_xboole_0(sK1,sK2) = k9_subset_1(sK0,k4_xboole_0(sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f813,f1703])).

fof(f1703,plain,(
    ! [X18] : k4_xboole_0(X18,sK2) = k4_xboole_0(X18,k9_subset_1(sK0,X18,sK2)) ),
    inference(global_subsumption,[],[f53,f1559])).

fof(f1559,plain,(
    ! [X18] :
      ( k4_xboole_0(X18,sK2) = k4_xboole_0(X18,k9_subset_1(sK0,X18,sK2))
      | ~ r1_tarski(X18,X18) ) ),
    inference(superposition,[],[f234,f191])).

fof(f191,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f28,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f33])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f813,plain,(
    k9_subset_1(sK0,k4_xboole_0(sK1,sK2),sK1) = k4_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f501,f191])).

fof(f501,plain,(
    ! [X3] : k9_subset_1(sK0,X3,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,X3)) ),
    inference(superposition,[],[f190,f47])).

fof(f190,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK1) = k4_xboole_0(X0,k4_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f30,f51])).

fof(f125,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(sK0,X0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f30,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (8826)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (8834)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (8818)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (8827)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (8814)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (8842)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (8836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (8843)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (8816)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (8828)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (8815)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (8841)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (8835)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (8838)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (8817)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (8839)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (8819)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (8820)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (8825)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (8837)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (8832)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (8833)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (8829)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (8831)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (8831)Refutation not found, incomplete strategy% (8831)------------------------------
% 0.20/0.54  % (8831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8831)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8831)Memory used [KB]: 10618
% 0.20/0.54  % (8831)Time elapsed: 0.138 s
% 0.20/0.54  % (8831)------------------------------
% 0.20/0.54  % (8831)------------------------------
% 0.20/0.54  % (8830)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (8824)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (8823)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (8821)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (8840)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (8822)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.11/0.73  % (8844)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.42/0.81  % (8819)Time limit reached!
% 3.42/0.81  % (8819)------------------------------
% 3.42/0.81  % (8819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.81  % (8819)Termination reason: Time limit
% 3.42/0.81  
% 3.42/0.81  % (8819)Memory used [KB]: 9083
% 3.42/0.81  % (8819)Time elapsed: 0.420 s
% 3.42/0.81  % (8819)------------------------------
% 3.42/0.81  % (8819)------------------------------
% 4.15/0.90  % (8824)Time limit reached!
% 4.15/0.90  % (8824)------------------------------
% 4.15/0.90  % (8824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.90  % (8824)Termination reason: Time limit
% 4.15/0.90  
% 4.15/0.90  % (8824)Memory used [KB]: 13560
% 4.15/0.90  % (8824)Time elapsed: 0.508 s
% 4.15/0.90  % (8824)------------------------------
% 4.15/0.90  % (8824)------------------------------
% 4.15/0.92  % (8815)Time limit reached!
% 4.15/0.92  % (8815)------------------------------
% 4.15/0.92  % (8815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.92  % (8815)Termination reason: Time limit
% 4.15/0.92  
% 4.15/0.92  % (8815)Memory used [KB]: 8571
% 4.15/0.92  % (8815)Time elapsed: 0.517 s
% 4.15/0.92  % (8815)------------------------------
% 4.15/0.92  % (8815)------------------------------
% 4.42/0.94  % (8814)Time limit reached!
% 4.42/0.94  % (8814)------------------------------
% 4.42/0.94  % (8814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.94  % (8814)Termination reason: Time limit
% 4.42/0.94  
% 4.42/0.94  % (8814)Memory used [KB]: 4221
% 4.42/0.94  % (8814)Time elapsed: 0.509 s
% 4.42/0.94  % (8814)------------------------------
% 4.42/0.94  % (8814)------------------------------
% 4.42/0.94  % (8826)Time limit reached!
% 4.42/0.94  % (8826)------------------------------
% 4.42/0.94  % (8826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.95  % (8845)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.42/0.96  % (8826)Termination reason: Time limit
% 4.42/0.96  
% 4.42/0.96  % (8826)Memory used [KB]: 11513
% 4.42/0.96  % (8826)Time elapsed: 0.534 s
% 4.42/0.96  % (8826)------------------------------
% 4.42/0.96  % (8826)------------------------------
% 4.42/1.00  % (8821)Time limit reached!
% 4.42/1.00  % (8821)------------------------------
% 4.42/1.00  % (8821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/1.00  % (8821)Termination reason: Time limit
% 4.42/1.00  
% 4.42/1.00  % (8821)Memory used [KB]: 11001
% 4.42/1.00  % (8821)Time elapsed: 0.610 s
% 4.42/1.00  % (8821)------------------------------
% 4.42/1.00  % (8821)------------------------------
% 4.42/1.03  % (8842)Time limit reached!
% 4.42/1.03  % (8842)------------------------------
% 4.42/1.03  % (8842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/1.03  % (8842)Termination reason: Time limit
% 4.42/1.03  
% 4.42/1.03  % (8842)Memory used [KB]: 10362
% 4.42/1.03  % (8842)Time elapsed: 0.632 s
% 4.42/1.03  % (8842)------------------------------
% 4.42/1.03  % (8842)------------------------------
% 5.15/1.03  % (8847)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.15/1.04  % (8846)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.15/1.04  % (8830)Time limit reached!
% 5.15/1.04  % (8830)------------------------------
% 5.15/1.04  % (8830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.15/1.04  % (8830)Termination reason: Time limit
% 5.15/1.04  
% 5.15/1.04  % (8830)Memory used [KB]: 18805
% 5.15/1.04  % (8830)Time elapsed: 0.639 s
% 5.15/1.04  % (8830)------------------------------
% 5.15/1.04  % (8830)------------------------------
% 5.15/1.06  % (8848)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.55/1.10  % (8849)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.55/1.15  % (8850)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.55/1.15  % (8838)Refutation found. Thanks to Tanya!
% 5.55/1.15  % SZS status Theorem for theBenchmark
% 5.55/1.15  % SZS output start Proof for theBenchmark
% 5.55/1.16  fof(f5233,plain,(
% 5.55/1.16    $false),
% 5.55/1.16    inference(global_subsumption,[],[f2795,f5232])).
% 5.55/1.16  fof(f5232,plain,(
% 5.55/1.16    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(trivial_inequality_removal,[],[f5179])).
% 5.55/1.16  fof(f5179,plain,(
% 5.55/1.16    k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(backward_demodulation,[],[f443,f5178])).
% 5.55/1.16  fof(f5178,plain,(
% 5.55/1.16    ( ! [X56] : (k4_xboole_0(sK0,k4_xboole_0(X56,sK2)) = k2_xboole_0(sK2,k4_xboole_0(sK0,X56))) )),
% 5.55/1.16    inference(forward_demodulation,[],[f5078,f31])).
% 5.55/1.16  fof(f31,plain,(
% 5.55/1.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.55/1.16    inference(cnf_transformation,[],[f1])).
% 5.55/1.16  fof(f1,axiom,(
% 5.55/1.16    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.55/1.16  fof(f5078,plain,(
% 5.55/1.16    ( ! [X56] : (k4_xboole_0(sK0,k4_xboole_0(X56,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X56),sK2)) )),
% 5.55/1.16    inference(superposition,[],[f3192,f123])).
% 5.55/1.16  fof(f123,plain,(
% 5.55/1.16    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 5.55/1.16    inference(unit_resulting_resolution,[],[f122,f48])).
% 5.55/1.16  fof(f48,plain,(
% 5.55/1.16    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 5.55/1.16    inference(definition_unfolding,[],[f34,f33])).
% 5.55/1.16  fof(f33,plain,(
% 5.55/1.16    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.55/1.16    inference(cnf_transformation,[],[f5])).
% 5.55/1.16  fof(f5,axiom,(
% 5.55/1.16    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.55/1.16  fof(f34,plain,(
% 5.55/1.16    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 5.55/1.16    inference(cnf_transformation,[],[f18])).
% 5.55/1.16  fof(f18,plain,(
% 5.55/1.16    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 5.55/1.16    inference(ennf_transformation,[],[f4])).
% 5.55/1.16  fof(f4,axiom,(
% 5.55/1.16    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 5.55/1.16  fof(f122,plain,(
% 5.55/1.16    r1_tarski(sK2,sK0)),
% 5.55/1.16    inference(duplicate_literal_removal,[],[f120])).
% 5.55/1.16  fof(f120,plain,(
% 5.55/1.16    r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0)),
% 5.55/1.16    inference(resolution,[],[f64,f40])).
% 5.55/1.16  fof(f40,plain,(
% 5.55/1.16    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 5.55/1.16    inference(cnf_transformation,[],[f22])).
% 5.55/1.16  fof(f22,plain,(
% 5.55/1.16    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 5.55/1.16    inference(ennf_transformation,[],[f3])).
% 5.55/1.16  fof(f3,axiom,(
% 5.55/1.16    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 5.55/1.16  fof(f64,plain,(
% 5.55/1.16    ( ! [X0] : (r2_hidden(sK3(sK2,X0),sK0) | r1_tarski(sK2,X0)) )),
% 5.55/1.16    inference(resolution,[],[f57,f39])).
% 5.55/1.16  fof(f39,plain,(
% 5.55/1.16    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 5.55/1.16    inference(cnf_transformation,[],[f22])).
% 5.55/1.16  fof(f57,plain,(
% 5.55/1.16    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK0)) )),
% 5.55/1.16    inference(resolution,[],[f37,f28])).
% 5.55/1.16  fof(f28,plain,(
% 5.55/1.16    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(cnf_transformation,[],[f17])).
% 5.55/1.16  fof(f17,plain,(
% 5.55/1.16    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.55/1.16    inference(ennf_transformation,[],[f16])).
% 5.55/1.16  fof(f16,negated_conjecture,(
% 5.55/1.16    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 5.55/1.16    inference(negated_conjecture,[],[f15])).
% 5.55/1.16  fof(f15,conjecture,(
% 5.55/1.16    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).
% 5.55/1.16  fof(f37,plain,(
% 5.55/1.16    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 5.55/1.16    inference(cnf_transformation,[],[f21])).
% 5.55/1.16  fof(f21,plain,(
% 5.55/1.16    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.55/1.16    inference(ennf_transformation,[],[f11])).
% 5.55/1.16  fof(f11,axiom,(
% 5.55/1.16    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 5.55/1.16  fof(f3192,plain,(
% 5.55/1.16    ( ! [X6,X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X6),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = k4_xboole_0(X4,k4_xboole_0(X6,X5))) )),
% 5.55/1.16    inference(backward_demodulation,[],[f288,f3186])).
% 5.55/1.16  fof(f3186,plain,(
% 5.55/1.16    ( ! [X41,X42,X40] : (k4_xboole_0(X40,k4_xboole_0(X41,X42)) = k4_xboole_0(X40,k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X40,X42))))) )),
% 5.55/1.16    inference(global_subsumption,[],[f53,f3185])).
% 5.55/1.16  fof(f3185,plain,(
% 5.55/1.16    ( ! [X41,X42,X40] : (k4_xboole_0(X40,k4_xboole_0(X41,X42)) = k4_xboole_0(X40,k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X40,X42)))) | ~r1_tarski(X40,X40)) )),
% 5.55/1.16    inference(forward_demodulation,[],[f2990,f49])).
% 5.55/1.16  fof(f49,plain,(
% 5.55/1.16    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 5.55/1.16    inference(definition_unfolding,[],[f41,f33,f33])).
% 5.55/1.16  fof(f41,plain,(
% 5.55/1.16    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.55/1.16    inference(cnf_transformation,[],[f6])).
% 5.55/1.16  fof(f6,axiom,(
% 5.55/1.16    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.55/1.16  fof(f2990,plain,(
% 5.55/1.16    ( ! [X41,X42,X40] : (k4_xboole_0(X40,k4_xboole_0(X41,X42)) = k4_xboole_0(X40,k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,X40)),X42)) | ~r1_tarski(X40,X40)) )),
% 5.55/1.16    inference(superposition,[],[f234,f232])).
% 5.55/1.16  fof(f232,plain,(
% 5.55/1.16    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6))) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X6)) )),
% 5.55/1.16    inference(superposition,[],[f49,f47])).
% 5.55/1.16  fof(f47,plain,(
% 5.55/1.16    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 5.55/1.16    inference(definition_unfolding,[],[f32,f33,f33])).
% 5.55/1.16  fof(f32,plain,(
% 5.55/1.16    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.55/1.16    inference(cnf_transformation,[],[f2])).
% 5.55/1.16  fof(f2,axiom,(
% 5.55/1.16    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.55/1.16  fof(f234,plain,(
% 5.55/1.16    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,X12))) = k4_xboole_0(X10,X12) | ~r1_tarski(X10,X11)) )),
% 5.55/1.16    inference(superposition,[],[f49,f48])).
% 5.55/1.16  fof(f53,plain,(
% 5.55/1.16    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 5.55/1.16    inference(duplicate_literal_removal,[],[f52])).
% 5.55/1.16  fof(f52,plain,(
% 5.55/1.16    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 5.55/1.16    inference(resolution,[],[f40,f39])).
% 5.55/1.16  fof(f288,plain,(
% 5.55/1.16    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X4,X5)))) = k2_xboole_0(k4_xboole_0(X4,X6),k4_xboole_0(X5,k4_xboole_0(X5,X4)))) )),
% 5.55/1.16    inference(superposition,[],[f50,f47])).
% 5.55/1.16  fof(f50,plain,(
% 5.55/1.16    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 5.55/1.16    inference(definition_unfolding,[],[f42,f33])).
% 5.55/1.16  fof(f42,plain,(
% 5.55/1.16    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 5.55/1.16    inference(cnf_transformation,[],[f7])).
% 5.55/1.16  fof(f7,axiom,(
% 5.55/1.16    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).
% 5.55/1.16  fof(f443,plain,(
% 5.55/1.16    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(backward_demodulation,[],[f171,f441])).
% 5.55/1.16  fof(f441,plain,(
% 5.55/1.16    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 5.55/1.16    inference(forward_demodulation,[],[f425,f31])).
% 5.55/1.16  fof(f425,plain,(
% 5.55/1.16    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 5.55/1.16    inference(unit_resulting_resolution,[],[f93,f28,f46])).
% 5.55/1.16  fof(f46,plain,(
% 5.55/1.16    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.55/1.16    inference(cnf_transformation,[],[f27])).
% 5.55/1.16  fof(f27,plain,(
% 5.55/1.16    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.55/1.16    inference(flattening,[],[f26])).
% 5.55/1.16  fof(f26,plain,(
% 5.55/1.16    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.55/1.16    inference(ennf_transformation,[],[f12])).
% 5.55/1.16  fof(f12,axiom,(
% 5.55/1.16    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 5.55/1.16  fof(f93,plain,(
% 5.55/1.16    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(backward_demodulation,[],[f56,f72])).
% 5.55/1.16  fof(f72,plain,(
% 5.55/1.16    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 5.55/1.16    inference(unit_resulting_resolution,[],[f30,f36])).
% 5.55/1.16  fof(f36,plain,(
% 5.55/1.16    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.55/1.16    inference(cnf_transformation,[],[f20])).
% 5.55/1.16  fof(f20,plain,(
% 5.55/1.16    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.55/1.16    inference(ennf_transformation,[],[f8])).
% 5.55/1.16  fof(f8,axiom,(
% 5.55/1.16    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 5.55/1.16  fof(f30,plain,(
% 5.55/1.16    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(cnf_transformation,[],[f17])).
% 5.55/1.16  fof(f56,plain,(
% 5.55/1.16    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(unit_resulting_resolution,[],[f30,f35])).
% 5.55/1.16  fof(f35,plain,(
% 5.55/1.16    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.55/1.16    inference(cnf_transformation,[],[f19])).
% 5.55/1.16  fof(f19,plain,(
% 5.55/1.16    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.55/1.16    inference(ennf_transformation,[],[f9])).
% 5.55/1.16  fof(f9,axiom,(
% 5.55/1.16    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 5.55/1.16  fof(f171,plain,(
% 5.55/1.16    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(forward_demodulation,[],[f169,f166])).
% 5.55/1.16  fof(f166,plain,(
% 5.55/1.16    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0)) )),
% 5.55/1.16    inference(unit_resulting_resolution,[],[f30,f45])).
% 5.55/1.16  fof(f45,plain,(
% 5.55/1.16    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.55/1.16    inference(cnf_transformation,[],[f25])).
% 5.55/1.16  fof(f25,plain,(
% 5.55/1.16    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.55/1.16    inference(ennf_transformation,[],[f13])).
% 5.55/1.16  fof(f13,axiom,(
% 5.55/1.16    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 5.55/1.16  fof(f169,plain,(
% 5.55/1.16    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2)),
% 5.55/1.16    inference(backward_demodulation,[],[f107,f166])).
% 5.55/1.16  fof(f107,plain,(
% 5.55/1.16    k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) | ~m1_subset_1(k7_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(forward_demodulation,[],[f77,f72])).
% 5.55/1.16  fof(f77,plain,(
% 5.55/1.16    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) != k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2)) | ~m1_subset_1(k7_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(superposition,[],[f29,f36])).
% 5.55/1.16  fof(f29,plain,(
% 5.55/1.16    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)),
% 5.55/1.16    inference(cnf_transformation,[],[f17])).
% 5.55/1.16  fof(f2795,plain,(
% 5.55/1.16    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 5.55/1.16    inference(superposition,[],[f125,f1708])).
% 5.55/1.16  fof(f1708,plain,(
% 5.55/1.16    k4_xboole_0(sK1,sK2) = k9_subset_1(sK0,k4_xboole_0(sK1,sK2),sK1)),
% 5.55/1.16    inference(backward_demodulation,[],[f813,f1703])).
% 5.55/1.16  fof(f1703,plain,(
% 5.55/1.16    ( ! [X18] : (k4_xboole_0(X18,sK2) = k4_xboole_0(X18,k9_subset_1(sK0,X18,sK2))) )),
% 5.55/1.16    inference(global_subsumption,[],[f53,f1559])).
% 5.55/1.16  fof(f1559,plain,(
% 5.55/1.16    ( ! [X18] : (k4_xboole_0(X18,sK2) = k4_xboole_0(X18,k9_subset_1(sK0,X18,sK2)) | ~r1_tarski(X18,X18)) )),
% 5.55/1.16    inference(superposition,[],[f234,f191])).
% 5.55/1.16  fof(f191,plain,(
% 5.55/1.16    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2))) )),
% 5.55/1.16    inference(unit_resulting_resolution,[],[f28,f51])).
% 5.55/1.16  fof(f51,plain,(
% 5.55/1.16    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 5.55/1.16    inference(definition_unfolding,[],[f44,f33])).
% 5.55/1.16  fof(f44,plain,(
% 5.55/1.16    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)) )),
% 5.55/1.16    inference(cnf_transformation,[],[f24])).
% 5.55/1.16  fof(f24,plain,(
% 5.55/1.16    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 5.55/1.16    inference(ennf_transformation,[],[f14])).
% 5.55/1.16  fof(f14,axiom,(
% 5.55/1.16    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 5.55/1.16  fof(f813,plain,(
% 5.55/1.16    k9_subset_1(sK0,k4_xboole_0(sK1,sK2),sK1) = k4_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2))),
% 5.55/1.16    inference(superposition,[],[f501,f191])).
% 5.55/1.16  fof(f501,plain,(
% 5.55/1.16    ( ! [X3] : (k9_subset_1(sK0,X3,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,X3))) )),
% 5.55/1.16    inference(superposition,[],[f190,f47])).
% 5.55/1.16  fof(f190,plain,(
% 5.55/1.16    ( ! [X0] : (k9_subset_1(sK0,X0,sK1) = k4_xboole_0(X0,k4_xboole_0(X0,sK1))) )),
% 5.55/1.16    inference(unit_resulting_resolution,[],[f30,f51])).
% 5.55/1.16  fof(f125,plain,(
% 5.55/1.16    ( ! [X0] : (m1_subset_1(k9_subset_1(sK0,X0,sK1),k1_zfmisc_1(sK0))) )),
% 5.55/1.16    inference(unit_resulting_resolution,[],[f30,f43])).
% 5.55/1.16  fof(f43,plain,(
% 5.55/1.16    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 5.55/1.16    inference(cnf_transformation,[],[f23])).
% 5.55/1.16  fof(f23,plain,(
% 5.55/1.16    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 5.55/1.16    inference(ennf_transformation,[],[f10])).
% 5.55/1.16  fof(f10,axiom,(
% 5.55/1.16    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 5.55/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 5.55/1.16  % SZS output end Proof for theBenchmark
% 5.55/1.16  % (8838)------------------------------
% 5.55/1.16  % (8838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.55/1.16  % (8838)Termination reason: Refutation
% 5.55/1.16  
% 5.55/1.16  % (8838)Memory used [KB]: 14839
% 5.55/1.16  % (8838)Time elapsed: 0.726 s
% 5.55/1.16  % (8838)------------------------------
% 5.55/1.16  % (8838)------------------------------
% 6.39/1.18  % (8851)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.39/1.18  % (8813)Success in time 0.82 s
%------------------------------------------------------------------------------
