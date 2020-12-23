%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:59 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 675 expanded)
%              Number of leaves         :   25 ( 219 expanded)
%              Depth                    :   23
%              Number of atoms          :  160 ( 836 expanded)
%              Number of equality atoms :   99 ( 616 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f691,plain,(
    $false ),
    inference(global_subsumption,[],[f300,f690])).

fof(f690,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f661,f592])).

fof(f592,plain,(
    sK0 = k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f591,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f591,plain,(
    k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f590,f215])).

fof(f215,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f199,f214])).

fof(f214,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f204,f42])).

fof(f204,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f78,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f199,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f78,f79])).

fof(f590,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f589,f177])).

fof(f177,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f63,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f589,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f588,f42])).

fof(f588,plain,(
    k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f543,f218])).

fof(f218,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f79,f214])).

fof(f543,plain,(
    k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f499,f431])).

fof(f431,plain,(
    sK1 = k4_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f430,f214])).

fof(f430,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f412,f218])).

fof(f412,plain,(
    k4_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f393,f299])).

fof(f299,plain,(
    sK1 = k4_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f282,f292])).

fof(f292,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f78,f282])).

fof(f282,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f255,f214])).

fof(f255,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f81,f228])).

fof(f228,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f207,f215])).

fof(f207,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f78,f143])).

fof(f143,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f129,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f50])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f129,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f122,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f122,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f37,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f46,f50,f50])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f393,plain,(
    ! [X20] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X20))) = k4_xboole_0(sK1,X20) ),
    inference(forward_demodulation,[],[f355,f214])).

fof(f355,plain,(
    ! [X20] : k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X20))) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X20) ),
    inference(superposition,[],[f84,f228])).

fof(f84,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f64,f50,f50])).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f499,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f82,f494])).

fof(f494,plain,(
    ! [X2,X3] : k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f460,f263])).

fof(f263,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f78,f81])).

fof(f460,plain,(
    ! [X2,X3] : k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f82,f63])).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f77,f50])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f661,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f318,f37,f498])).

fof(f498,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f87,f494])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f67,f77])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f318,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f135,f292])).

fof(f135,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f39,f105,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,(
    ! [X0,X1] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f44,f89])).

fof(f89,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f300,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f165,f292])).

fof(f165,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f90,f161])).

fof(f161,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f37,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f90,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f38,f40])).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f38,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:14:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (25589)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (25585)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (25584)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (25594)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.26/0.53  % (25591)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.26/0.53  % (25601)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.26/0.53  % (25602)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.53  % (25599)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.26/0.53  % (25583)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.53  % (25595)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.53  % (25606)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.54  % (25603)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.26/0.54  % (25594)Refutation not found, incomplete strategy% (25594)------------------------------
% 1.26/0.54  % (25594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (25594)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (25594)Memory used [KB]: 10618
% 1.26/0.54  % (25594)Time elapsed: 0.126 s
% 1.26/0.54  % (25594)------------------------------
% 1.26/0.54  % (25594)------------------------------
% 1.36/0.54  % (25587)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.54  % (25609)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (25593)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.54  % (25605)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.54  % (25593)Refutation not found, incomplete strategy% (25593)------------------------------
% 1.36/0.54  % (25593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (25593)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (25593)Memory used [KB]: 10618
% 1.36/0.54  % (25593)Time elapsed: 0.135 s
% 1.36/0.54  % (25593)------------------------------
% 1.36/0.54  % (25593)------------------------------
% 1.36/0.54  % (25605)Refutation not found, incomplete strategy% (25605)------------------------------
% 1.36/0.54  % (25605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (25605)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (25605)Memory used [KB]: 10746
% 1.36/0.54  % (25605)Time elapsed: 0.124 s
% 1.36/0.54  % (25605)------------------------------
% 1.36/0.54  % (25605)------------------------------
% 1.36/0.54  % (25588)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.55  % (25607)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (25590)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.55  % (25612)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (25598)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.55  % (25597)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % (25598)Refutation not found, incomplete strategy% (25598)------------------------------
% 1.36/0.55  % (25598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (25598)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (25598)Memory used [KB]: 6140
% 1.36/0.55  % (25598)Time elapsed: 0.002 s
% 1.36/0.55  % (25598)------------------------------
% 1.36/0.55  % (25598)------------------------------
% 1.36/0.55  % (25600)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (25586)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.55  % (25600)Refutation not found, incomplete strategy% (25600)------------------------------
% 1.36/0.55  % (25600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (25600)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (25600)Memory used [KB]: 10618
% 1.36/0.55  % (25600)Time elapsed: 0.148 s
% 1.36/0.55  % (25600)------------------------------
% 1.36/0.55  % (25600)------------------------------
% 1.36/0.55  % (25604)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (25611)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.56  % (25596)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.57  % (25592)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.57  % (25608)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.58  % (25610)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.60  % (25607)Refutation found. Thanks to Tanya!
% 1.36/0.60  % SZS status Theorem for theBenchmark
% 1.36/0.61  % SZS output start Proof for theBenchmark
% 1.36/0.61  fof(f691,plain,(
% 1.36/0.61    $false),
% 1.36/0.61    inference(global_subsumption,[],[f300,f690])).
% 1.36/0.61  fof(f690,plain,(
% 1.36/0.61    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.36/0.61    inference(forward_demodulation,[],[f661,f592])).
% 1.36/0.61  fof(f592,plain,(
% 1.36/0.61    sK0 = k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1))),
% 1.36/0.61    inference(forward_demodulation,[],[f591,f42])).
% 1.36/0.61  fof(f42,plain,(
% 1.36/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.61    inference(cnf_transformation,[],[f12])).
% 1.36/0.61  fof(f12,axiom,(
% 1.36/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.36/0.61  fof(f591,plain,(
% 1.36/0.61    k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1))),
% 1.36/0.61    inference(forward_demodulation,[],[f590,f215])).
% 1.36/0.61  fof(f215,plain,(
% 1.36/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.36/0.61    inference(backward_demodulation,[],[f199,f214])).
% 1.36/0.61  fof(f214,plain,(
% 1.36/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.61    inference(forward_demodulation,[],[f204,f42])).
% 1.36/0.61  fof(f204,plain,(
% 1.36/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.36/0.61    inference(superposition,[],[f78,f79])).
% 1.36/0.61  fof(f79,plain,(
% 1.36/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.36/0.61    inference(definition_unfolding,[],[f41,f50])).
% 1.36/0.61  fof(f50,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.36/0.61    inference(cnf_transformation,[],[f10])).
% 1.36/0.61  fof(f10,axiom,(
% 1.36/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.36/0.61  fof(f41,plain,(
% 1.36/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f8])).
% 1.36/0.61  fof(f8,axiom,(
% 1.36/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.36/0.61  fof(f78,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.36/0.61    inference(definition_unfolding,[],[f49,f50])).
% 1.36/0.61  fof(f49,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.61    inference(cnf_transformation,[],[f4])).
% 1.36/0.61  fof(f4,axiom,(
% 1.36/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.36/0.61  fof(f199,plain,(
% 1.36/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.36/0.61    inference(superposition,[],[f78,f79])).
% 1.36/0.61  fof(f590,plain,(
% 1.36/0.61    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1))),
% 1.36/0.61    inference(forward_demodulation,[],[f589,f177])).
% 1.36/0.61  fof(f177,plain,(
% 1.36/0.61    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 1.36/0.61    inference(superposition,[],[f63,f45])).
% 1.36/0.61  fof(f45,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f2])).
% 1.36/0.61  fof(f2,axiom,(
% 1.36/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.36/0.61  fof(f63,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.36/0.61    inference(cnf_transformation,[],[f13])).
% 1.36/0.61  fof(f13,axiom,(
% 1.36/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.36/0.61  fof(f589,plain,(
% 1.36/0.61    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1))),
% 1.36/0.61    inference(forward_demodulation,[],[f588,f42])).
% 1.36/0.61  fof(f588,plain,(
% 1.36/0.61    k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k1_xboole_0)),
% 1.36/0.61    inference(forward_demodulation,[],[f543,f218])).
% 1.36/0.61  fof(f218,plain,(
% 1.36/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.36/0.61    inference(backward_demodulation,[],[f79,f214])).
% 1.36/0.61  fof(f543,plain,(
% 1.36/0.61    k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK1))),
% 1.36/0.61    inference(superposition,[],[f499,f431])).
% 1.36/0.61  fof(f431,plain,(
% 1.36/0.61    sK1 = k4_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.36/0.61    inference(forward_demodulation,[],[f430,f214])).
% 1.36/0.61  fof(f430,plain,(
% 1.36/0.61    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.36/0.61    inference(forward_demodulation,[],[f412,f218])).
% 1.36/0.61  fof(f412,plain,(
% 1.36/0.61    k4_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 1.36/0.61    inference(superposition,[],[f393,f299])).
% 1.36/0.61  fof(f299,plain,(
% 1.36/0.61    sK1 = k4_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.36/0.61    inference(backward_demodulation,[],[f282,f292])).
% 1.36/0.61  fof(f292,plain,(
% 1.36/0.61    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.36/0.61    inference(superposition,[],[f78,f282])).
% 1.36/0.61  fof(f282,plain,(
% 1.36/0.61    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.36/0.61    inference(forward_demodulation,[],[f255,f214])).
% 1.36/0.61  fof(f255,plain,(
% 1.36/0.61    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.36/0.61    inference(superposition,[],[f81,f228])).
% 1.36/0.61  fof(f228,plain,(
% 1.36/0.61    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.36/0.61    inference(forward_demodulation,[],[f207,f215])).
% 1.36/0.61  fof(f207,plain,(
% 1.36/0.61    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 1.36/0.61    inference(superposition,[],[f78,f143])).
% 1.36/0.61  fof(f143,plain,(
% 1.36/0.61    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 1.36/0.61    inference(unit_resulting_resolution,[],[f129,f83])).
% 1.36/0.61  fof(f83,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.36/0.61    inference(definition_unfolding,[],[f56,f50])).
% 1.36/0.61  fof(f56,plain,(
% 1.36/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.36/0.61    inference(cnf_transformation,[],[f33])).
% 1.36/0.61  fof(f33,plain,(
% 1.36/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.36/0.61    inference(ennf_transformation,[],[f7])).
% 1.36/0.61  fof(f7,axiom,(
% 1.36/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.36/0.61  fof(f129,plain,(
% 1.36/0.61    r1_tarski(sK1,sK0)),
% 1.36/0.61    inference(unit_resulting_resolution,[],[f122,f88])).
% 1.36/0.61  fof(f88,plain,(
% 1.36/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.36/0.61    inference(equality_resolution,[],[f59])).
% 1.36/0.61  fof(f59,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.36/0.61    inference(cnf_transformation,[],[f21])).
% 1.36/0.61  fof(f21,axiom,(
% 1.36/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.36/0.61  fof(f122,plain,(
% 1.36/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.36/0.61    inference(unit_resulting_resolution,[],[f39,f37,f55])).
% 1.36/0.61  fof(f55,plain,(
% 1.36/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f32])).
% 1.36/0.61  fof(f32,plain,(
% 1.36/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.36/0.61    inference(ennf_transformation,[],[f23])).
% 1.36/0.61  fof(f23,axiom,(
% 1.36/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.36/0.61  fof(f37,plain,(
% 1.36/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.36/0.61    inference(cnf_transformation,[],[f31])).
% 1.36/0.61  fof(f31,plain,(
% 1.36/0.61    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.61    inference(ennf_transformation,[],[f29])).
% 1.36/0.61  fof(f29,negated_conjecture,(
% 1.36/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.36/0.61    inference(negated_conjecture,[],[f28])).
% 1.36/0.61  fof(f28,conjecture,(
% 1.36/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.36/0.61  fof(f39,plain,(
% 1.36/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.36/0.61    inference(cnf_transformation,[],[f26])).
% 1.36/0.61  fof(f26,axiom,(
% 1.36/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.36/0.61  fof(f81,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.36/0.61    inference(definition_unfolding,[],[f46,f50,f50])).
% 1.36/0.61  fof(f46,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f1])).
% 1.36/0.61  fof(f1,axiom,(
% 1.36/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.36/0.61  fof(f393,plain,(
% 1.36/0.61    ( ! [X20] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X20))) = k4_xboole_0(sK1,X20)) )),
% 1.36/0.61    inference(forward_demodulation,[],[f355,f214])).
% 1.36/0.61  fof(f355,plain,(
% 1.36/0.61    ( ! [X20] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X20))) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X20)) )),
% 1.36/0.61    inference(superposition,[],[f84,f228])).
% 1.36/0.61  fof(f84,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.36/0.61    inference(definition_unfolding,[],[f64,f50,f50])).
% 1.36/0.61  fof(f64,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f11])).
% 1.36/0.61  fof(f11,axiom,(
% 1.36/0.61    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.36/0.61  fof(f499,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.36/0.61    inference(backward_demodulation,[],[f82,f494])).
% 1.36/0.61  fof(f494,plain,(
% 1.36/0.61    ( ! [X2,X3] : (k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 1.36/0.61    inference(forward_demodulation,[],[f460,f263])).
% 1.36/0.61  fof(f263,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.36/0.61    inference(superposition,[],[f78,f81])).
% 1.36/0.61  fof(f460,plain,(
% 1.36/0.61    ( ! [X2,X3] : (k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) )),
% 1.36/0.61    inference(superposition,[],[f82,f63])).
% 1.36/0.61  fof(f82,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.36/0.61    inference(definition_unfolding,[],[f51,f77,f50])).
% 1.36/0.61  fof(f77,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.36/0.61    inference(definition_unfolding,[],[f47,f76])).
% 1.36/0.61  fof(f76,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.36/0.61    inference(definition_unfolding,[],[f48,f75])).
% 1.36/0.61  fof(f75,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.36/0.61    inference(definition_unfolding,[],[f62,f74])).
% 1.36/0.61  fof(f74,plain,(
% 1.36/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.36/0.61    inference(definition_unfolding,[],[f68,f73])).
% 1.36/0.61  fof(f73,plain,(
% 1.36/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.36/0.61    inference(definition_unfolding,[],[f69,f72])).
% 1.36/0.61  fof(f72,plain,(
% 1.36/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.36/0.61    inference(definition_unfolding,[],[f70,f71])).
% 1.36/0.61  fof(f71,plain,(
% 1.36/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f20])).
% 1.36/0.61  fof(f20,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.36/0.61  fof(f70,plain,(
% 1.36/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f19])).
% 1.36/0.61  fof(f19,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.36/0.61  fof(f69,plain,(
% 1.36/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f18])).
% 1.36/0.61  fof(f18,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.36/0.61  fof(f68,plain,(
% 1.36/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f17])).
% 1.36/0.61  fof(f17,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.36/0.61  fof(f62,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f16])).
% 1.36/0.61  fof(f16,axiom,(
% 1.36/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.61  fof(f48,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f15])).
% 1.36/0.61  fof(f15,axiom,(
% 1.36/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.61  fof(f47,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.36/0.61    inference(cnf_transformation,[],[f22])).
% 1.36/0.61  fof(f22,axiom,(
% 1.36/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.36/0.61  fof(f51,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.36/0.61    inference(cnf_transformation,[],[f14])).
% 1.36/0.61  fof(f14,axiom,(
% 1.36/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.36/0.61  fof(f661,plain,(
% 1.36/0.61    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(sK0,sK1),sK1))),
% 1.36/0.61    inference(unit_resulting_resolution,[],[f318,f37,f498])).
% 1.36/0.61  fof(f498,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.36/0.61    inference(backward_demodulation,[],[f87,f494])).
% 1.36/0.61  fof(f87,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 1.36/0.61    inference(definition_unfolding,[],[f67,f77])).
% 1.36/0.61  fof(f67,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f36])).
% 1.36/0.61  fof(f36,plain,(
% 1.36/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.61    inference(flattening,[],[f35])).
% 1.36/0.61  fof(f35,plain,(
% 1.36/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.36/0.61    inference(ennf_transformation,[],[f27])).
% 1.36/0.61  fof(f27,axiom,(
% 1.36/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.36/0.61  fof(f318,plain,(
% 1.36/0.61    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.36/0.61    inference(superposition,[],[f135,f292])).
% 1.36/0.61  fof(f135,plain,(
% 1.36/0.61    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.36/0.61    inference(unit_resulting_resolution,[],[f39,f105,f54])).
% 1.36/0.61  fof(f54,plain,(
% 1.36/0.61    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f32])).
% 1.36/0.61  fof(f105,plain,(
% 1.36/0.61    ( ! [X0,X1] : (r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.36/0.61    inference(unit_resulting_resolution,[],[f44,f89])).
% 1.36/0.61  fof(f89,plain,(
% 1.36/0.61    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.36/0.61    inference(equality_resolution,[],[f58])).
% 1.36/0.61  fof(f58,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.36/0.61    inference(cnf_transformation,[],[f21])).
% 1.36/0.61  fof(f44,plain,(
% 1.36/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f9])).
% 1.36/0.61  fof(f9,axiom,(
% 1.36/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.36/0.61  fof(f300,plain,(
% 1.36/0.61    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.36/0.61    inference(backward_demodulation,[],[f165,f292])).
% 1.36/0.61  fof(f165,plain,(
% 1.36/0.61    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.36/0.61    inference(backward_demodulation,[],[f90,f161])).
% 1.36/0.61  fof(f161,plain,(
% 1.36/0.61    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.36/0.61    inference(unit_resulting_resolution,[],[f37,f57])).
% 1.36/0.61  fof(f57,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.36/0.61    inference(cnf_transformation,[],[f34])).
% 1.36/0.61  fof(f34,plain,(
% 1.36/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.61    inference(ennf_transformation,[],[f25])).
% 1.36/0.61  fof(f25,axiom,(
% 1.36/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.36/0.61  fof(f90,plain,(
% 1.36/0.61    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.36/0.61    inference(backward_demodulation,[],[f38,f40])).
% 1.36/0.61  fof(f40,plain,(
% 1.36/0.61    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.36/0.61    inference(cnf_transformation,[],[f24])).
% 1.36/0.61  fof(f24,axiom,(
% 1.36/0.61    ! [X0] : k2_subset_1(X0) = X0),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.36/0.61  fof(f38,plain,(
% 1.36/0.61    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.36/0.61    inference(cnf_transformation,[],[f31])).
% 1.36/0.61  % SZS output end Proof for theBenchmark
% 1.36/0.61  % (25607)------------------------------
% 1.36/0.61  % (25607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.61  % (25607)Termination reason: Refutation
% 1.36/0.61  
% 1.36/0.61  % (25607)Memory used [KB]: 6908
% 1.36/0.61  % (25607)Time elapsed: 0.203 s
% 1.36/0.61  % (25607)------------------------------
% 1.36/0.61  % (25607)------------------------------
% 1.36/0.61  % (25582)Success in time 0.25 s
%------------------------------------------------------------------------------
