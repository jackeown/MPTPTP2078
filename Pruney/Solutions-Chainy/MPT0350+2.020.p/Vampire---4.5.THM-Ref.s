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
% DateTime   : Thu Dec  3 12:43:52 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 533 expanded)
%              Number of leaves         :   22 ( 158 expanded)
%              Depth                    :   16
%              Number of atoms          :  158 ( 861 expanded)
%              Number of equality atoms :   76 ( 372 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(global_subsumption,[],[f76,f319])).

fof(f319,plain,(
    sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f318,f310])).

fof(f310,plain,(
    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f309,f308])).

fof(f308,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f224,f306])).

fof(f306,plain,(
    ! [X2] : k4_subset_1(X2,X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f305,f196])).

fof(f196,plain,(
    ! [X2] : k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = X2 ),
    inference(superposition,[],[f70,f100])).

fof(f100,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f99,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f99,plain,(
    ! [X2] : r1_tarski(X2,X2) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X2] :
      ( r1_tarski(X2,X2)
      | r1_tarski(X2,X2) ) ),
    inference(resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f38,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f305,plain,(
    ! [X2] : k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k4_subset_1(X2,X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f304,f224])).

fof(f304,plain,(
    ! [X2] : k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f295,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f295,plain,(
    ! [X2] : k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k5_xboole_0(X2,X2))) ),
    inference(superposition,[],[f71,f100])).

fof(f71,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f42,f68,f41,f68])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f224,plain,(
    ! [X0] : k4_subset_1(X0,X0,k1_xboole_0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f101,f147,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f147,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f122,f146])).

fof(f146,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f145,f36])).

fof(f145,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f140,f100])).

fof(f140,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f101,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f41])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f122,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f101,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f101,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f99,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(global_subsumption,[],[f34,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f45,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f309,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f296,f36])).

fof(f296,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f71,f92])).

fof(f92,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f88,f47])).

fof(f88,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f84,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f32,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f318,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f317,f69])).

fof(f69,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f67,f67])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f317,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) ),
    inference(forward_demodulation,[],[f299,f235])).

fof(f235,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f32,f121,f73])).

fof(f121,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f32,f48])).

fof(f299,plain,(
    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f71,f139])).

fof(f139,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f72])).

fof(f76,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f33,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f33,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (18012)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (18018)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (17998)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (17989)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (18014)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.54  % (17990)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.54  % (17991)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.54  % (17993)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.54  % (18002)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.54  % (17996)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.54  % (17992)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.55  % (18013)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.55  % (18010)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (18015)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.55  % (17997)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.55  % (18006)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.55  % (18012)Refutation not found, incomplete strategy% (18012)------------------------------
% 1.38/0.55  % (18012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (18008)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.55  % (18017)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (18012)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (18012)Memory used [KB]: 10746
% 1.38/0.55  % (18012)Time elapsed: 0.136 s
% 1.38/0.55  % (18012)------------------------------
% 1.38/0.55  % (18012)------------------------------
% 1.38/0.55  % (18004)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.55  % (18005)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.56  % (18009)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.56  % (17999)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.51/0.56  % (18016)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.56  % (18000)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.51/0.56  % (18007)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.56  % (18007)Refutation not found, incomplete strategy% (18007)------------------------------
% 1.51/0.56  % (18007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (18007)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (18007)Memory used [KB]: 10618
% 1.51/0.56  % (18007)Time elapsed: 0.145 s
% 1.51/0.56  % (18007)------------------------------
% 1.51/0.56  % (18007)------------------------------
% 1.51/0.56  % (18001)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.51/0.56  % (17995)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.51/0.57  % (18014)Refutation found. Thanks to Tanya!
% 1.51/0.57  % SZS status Theorem for theBenchmark
% 1.51/0.57  % SZS output start Proof for theBenchmark
% 1.51/0.57  fof(f320,plain,(
% 1.51/0.57    $false),
% 1.51/0.57    inference(global_subsumption,[],[f76,f319])).
% 1.51/0.57  fof(f319,plain,(
% 1.51/0.57    sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.51/0.57    inference(forward_demodulation,[],[f318,f310])).
% 1.51/0.57  fof(f310,plain,(
% 1.51/0.57    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.51/0.57    inference(forward_demodulation,[],[f309,f308])).
% 1.51/0.57  fof(f308,plain,(
% 1.51/0.57    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.51/0.57    inference(backward_demodulation,[],[f224,f306])).
% 1.51/0.57  fof(f306,plain,(
% 1.51/0.57    ( ! [X2] : (k4_subset_1(X2,X2,k1_xboole_0) = X2) )),
% 1.51/0.57    inference(forward_demodulation,[],[f305,f196])).
% 1.51/0.57  fof(f196,plain,(
% 1.51/0.57    ( ! [X2] : (k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = X2) )),
% 1.51/0.57    inference(superposition,[],[f70,f100])).
% 1.51/0.57  fof(f100,plain,(
% 1.51/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f99,f47])).
% 1.51/0.57  fof(f47,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f26])).
% 1.51/0.57  fof(f26,plain,(
% 1.51/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.51/0.57    inference(ennf_transformation,[],[f4])).
% 1.51/0.57  fof(f4,axiom,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.51/0.57  fof(f99,plain,(
% 1.51/0.57    ( ! [X2] : (r1_tarski(X2,X2)) )),
% 1.51/0.57    inference(duplicate_literal_removal,[],[f98])).
% 1.51/0.57  fof(f98,plain,(
% 1.51/0.57    ( ! [X2] : (r1_tarski(X2,X2) | r1_tarski(X2,X2)) )),
% 1.51/0.57    inference(resolution,[],[f52,f51])).
% 1.51/0.57  fof(f51,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f29])).
% 1.51/0.57  fof(f29,plain,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f1])).
% 1.51/0.57  fof(f1,axiom,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.57  fof(f52,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f29])).
% 1.51/0.57  fof(f70,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.51/0.57    inference(definition_unfolding,[],[f38,f68])).
% 1.51/0.57  fof(f68,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f40,f67])).
% 1.51/0.57  fof(f67,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f39,f66])).
% 1.51/0.57  fof(f66,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f57,f65])).
% 1.51/0.57  fof(f65,plain,(
% 1.51/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f59,f64])).
% 1.51/0.57  fof(f64,plain,(
% 1.51/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f60,f63])).
% 1.51/0.57  fof(f63,plain,(
% 1.51/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f61,f62])).
% 1.51/0.57  fof(f62,plain,(
% 1.51/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f13])).
% 1.51/0.57  fof(f13,axiom,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.51/0.57  fof(f61,plain,(
% 1.51/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f12])).
% 1.51/0.57  fof(f12,axiom,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.51/0.57  fof(f60,plain,(
% 1.51/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f11])).
% 1.51/0.57  fof(f11,axiom,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.51/0.57  fof(f59,plain,(
% 1.51/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f10])).
% 1.51/0.57  fof(f10,axiom,(
% 1.51/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.51/0.57  fof(f57,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f9])).
% 1.51/0.57  fof(f9,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.51/0.57  fof(f39,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f8])).
% 1.51/0.57  fof(f8,axiom,(
% 1.51/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.51/0.57  fof(f40,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f15])).
% 1.51/0.57  fof(f15,axiom,(
% 1.51/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.51/0.57  fof(f38,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.51/0.57    inference(cnf_transformation,[],[f3])).
% 1.51/0.57  fof(f3,axiom,(
% 1.51/0.57    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.51/0.57  fof(f305,plain,(
% 1.51/0.57    ( ! [X2] : (k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k4_subset_1(X2,X2,k1_xboole_0)) )),
% 1.51/0.57    inference(forward_demodulation,[],[f304,f224])).
% 1.51/0.57  fof(f304,plain,(
% 1.51/0.57    ( ! [X2] : (k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k1_xboole_0))) )),
% 1.51/0.57    inference(forward_demodulation,[],[f295,f36])).
% 1.51/0.57  fof(f36,plain,(
% 1.51/0.57    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.51/0.57    inference(cnf_transformation,[],[f6])).
% 1.51/0.57  fof(f6,axiom,(
% 1.51/0.57    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.51/0.57  fof(f295,plain,(
% 1.51/0.57    ( ! [X2] : (k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k5_xboole_0(X2,X2)))) )),
% 1.51/0.57    inference(superposition,[],[f71,f100])).
% 1.51/0.57  fof(f71,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f42,f68,f41,f68])).
% 1.51/0.57  fof(f41,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f2])).
% 1.51/0.57  fof(f2,axiom,(
% 1.51/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.51/0.57  fof(f42,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f5])).
% 1.51/0.57  fof(f5,axiom,(
% 1.51/0.57    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.51/0.57  fof(f224,plain,(
% 1.51/0.57    ( ! [X0] : (k4_subset_1(X0,X0,k1_xboole_0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f101,f147,f73])).
% 1.51/0.57  fof(f73,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f58,f68])).
% 1.51/0.57  fof(f58,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f31])).
% 1.51/0.57  fof(f31,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.57    inference(flattening,[],[f30])).
% 1.51/0.57  fof(f30,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.51/0.57    inference(ennf_transformation,[],[f21])).
% 1.51/0.57  fof(f21,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.51/0.57  fof(f147,plain,(
% 1.51/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.51/0.57    inference(backward_demodulation,[],[f122,f146])).
% 1.51/0.57  fof(f146,plain,(
% 1.51/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.51/0.57    inference(forward_demodulation,[],[f145,f36])).
% 1.51/0.57  fof(f145,plain,(
% 1.51/0.57    ( ! [X0] : (k5_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 1.51/0.57    inference(forward_demodulation,[],[f140,f100])).
% 1.51/0.57  fof(f140,plain,(
% 1.51/0.57    ( ! [X0] : (k3_subset_1(X0,X0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f101,f72])).
% 1.51/0.57  fof(f72,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f49,f41])).
% 1.51/0.57  fof(f49,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f28])).
% 1.51/0.57  fof(f28,plain,(
% 1.51/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f18])).
% 1.51/0.57  fof(f18,axiom,(
% 1.51/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.51/0.57  fof(f122,plain,(
% 1.51/0.57    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0))) )),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f101,f48])).
% 1.51/0.57  fof(f48,plain,(
% 1.51/0.57    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f27])).
% 1.51/0.57  fof(f27,plain,(
% 1.51/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f19])).
% 1.51/0.57  fof(f19,axiom,(
% 1.51/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.51/0.57  fof(f101,plain,(
% 1.51/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f99,f82])).
% 1.51/0.57  fof(f82,plain,(
% 1.51/0.57    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 1.51/0.57    inference(global_subsumption,[],[f34,f81])).
% 1.51/0.57  fof(f81,plain,(
% 1.51/0.57    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 1.51/0.57    inference(resolution,[],[f45,f75])).
% 1.51/0.57  fof(f75,plain,(
% 1.51/0.57    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.51/0.57    inference(equality_resolution,[],[f53])).
% 1.51/0.57  fof(f53,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f14])).
% 1.51/0.57  fof(f14,axiom,(
% 1.51/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.51/0.57  fof(f45,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f25])).
% 1.51/0.57  fof(f25,plain,(
% 1.51/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f16])).
% 1.51/0.57  fof(f16,axiom,(
% 1.51/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.51/0.57  fof(f34,plain,(
% 1.51/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f20])).
% 1.51/0.57  fof(f20,axiom,(
% 1.51/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.51/0.57  fof(f309,plain,(
% 1.51/0.57    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0))),
% 1.51/0.57    inference(forward_demodulation,[],[f296,f36])).
% 1.51/0.57  fof(f296,plain,(
% 1.51/0.57    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK1,sK1)))),
% 1.51/0.57    inference(superposition,[],[f71,f92])).
% 1.51/0.57  fof(f92,plain,(
% 1.51/0.57    sK1 = k3_xboole_0(sK1,sK0)),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f88,f47])).
% 1.51/0.57  fof(f88,plain,(
% 1.51/0.57    r1_tarski(sK1,sK0)),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f84,f74])).
% 1.51/0.57  fof(f74,plain,(
% 1.51/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.51/0.57    inference(equality_resolution,[],[f54])).
% 1.51/0.57  fof(f54,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f14])).
% 1.51/0.57  fof(f84,plain,(
% 1.51/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f34,f32,f46])).
% 1.51/0.57  fof(f46,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f25])).
% 1.51/0.57  fof(f32,plain,(
% 1.51/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.51/0.57    inference(cnf_transformation,[],[f24])).
% 1.51/0.57  fof(f24,plain,(
% 1.51/0.57    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f23])).
% 1.51/0.57  fof(f23,negated_conjecture,(
% 1.51/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.51/0.57    inference(negated_conjecture,[],[f22])).
% 1.51/0.57  fof(f22,conjecture,(
% 1.51/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.51/0.57  fof(f318,plain,(
% 1.51/0.57    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.51/0.57    inference(forward_demodulation,[],[f317,f69])).
% 1.51/0.57  fof(f69,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f37,f67,f67])).
% 1.51/0.57  fof(f37,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f7])).
% 1.51/0.57  fof(f7,axiom,(
% 1.51/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.51/0.57  fof(f317,plain,(
% 1.51/0.57    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))),
% 1.51/0.57    inference(forward_demodulation,[],[f299,f235])).
% 1.51/0.57  fof(f235,plain,(
% 1.51/0.57    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1)))),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f32,f121,f73])).
% 1.51/0.57  fof(f121,plain,(
% 1.51/0.57    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f32,f48])).
% 1.51/0.57  fof(f299,plain,(
% 1.51/0.57    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1)))),
% 1.51/0.57    inference(superposition,[],[f71,f139])).
% 1.51/0.57  fof(f139,plain,(
% 1.51/0.57    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f32,f72])).
% 1.51/0.57  fof(f76,plain,(
% 1.51/0.57    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.51/0.57    inference(backward_demodulation,[],[f33,f35])).
% 1.51/0.57  fof(f35,plain,(
% 1.51/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.51/0.57    inference(cnf_transformation,[],[f17])).
% 1.51/0.57  fof(f17,axiom,(
% 1.51/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.51/0.57  fof(f33,plain,(
% 1.51/0.57    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.51/0.57    inference(cnf_transformation,[],[f24])).
% 1.51/0.57  % SZS output end Proof for theBenchmark
% 1.51/0.57  % (18014)------------------------------
% 1.51/0.57  % (18014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (18014)Termination reason: Refutation
% 1.51/0.57  
% 1.51/0.57  % (18014)Memory used [KB]: 6524
% 1.51/0.57  % (18014)Time elapsed: 0.148 s
% 1.51/0.57  % (18014)------------------------------
% 1.51/0.57  % (18014)------------------------------
% 1.51/0.57  % (17988)Success in time 0.199 s
%------------------------------------------------------------------------------
