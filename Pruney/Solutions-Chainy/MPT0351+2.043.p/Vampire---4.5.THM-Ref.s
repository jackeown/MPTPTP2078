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
% DateTime   : Thu Dec  3 12:44:09 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   90 (1041 expanded)
%              Number of leaves         :   13 ( 310 expanded)
%              Depth                    :   22
%              Number of atoms          :  180 (1748 expanded)
%              Number of equality atoms :   61 ( 883 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f677,plain,(
    $false ),
    inference(subsumption_resolution,[],[f676,f277])).

fof(f277,plain,(
    sK0 != k4_subset_1(sK0,sK0,sK1) ),
    inference(superposition,[],[f62,f268])).

fof(f268,plain,(
    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f261,f132])).

fof(f132,plain,(
    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(resolution,[],[f127,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f24,f23])).

fof(f23,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1)) ) ),
    inference(resolution,[],[f50,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f261,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f257,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f25,f48,f48])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f257,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) ),
    inference(resolution,[],[f128,f20])).

fof(f128,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X2,X1,X2) ) ),
    inference(resolution,[],[f50,f63])).

fof(f62,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f21,f23])).

fof(f21,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f676,plain,(
    sK0 = k4_subset_1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f132,f675])).

fof(f675,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(subsumption_resolution,[],[f674,f650])).

fof(f650,plain,(
    ! [X8] :
      ( r2_hidden(sK4(X8,sK1,X8),sK0)
      | k3_tarski(k2_enumset1(X8,X8,X8,sK1)) = X8 ) ),
    inference(forward_demodulation,[],[f649,f510])).

fof(f510,plain,(
    sK1 = k4_subset_1(sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f285,f451])).

fof(f451,plain,(
    ! [X0] : k4_subset_1(X0,X0,X0) = X0 ),
    inference(backward_demodulation,[],[f258,f450])).

fof(f450,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(subsumption_resolution,[],[f449,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f449,plain,(
    ! [X0] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0
      | ~ r2_hidden(sK4(X0,X0,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f433])).

fof(f433,plain,(
    ! [X0] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0
      | ~ r2_hidden(sK4(X0,X0,X0),X0)
      | k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ) ),
    inference(resolution,[],[f373,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f373,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X3)
      | k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X2 ) ),
    inference(subsumption_resolution,[],[f365,f56])).

fof(f365,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X2)
      | r2_hidden(sK4(X2,X3,X2),X3)
      | k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X2 ) ),
    inference(factoring,[],[f54])).

fof(f258,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(resolution,[],[f128,f63])).

fof(f285,plain,(
    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1) ),
    inference(superposition,[],[f258,f131])).

fof(f131,plain,(
    k4_subset_1(sK0,sK1,sK1) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f127,f20])).

fof(f649,plain,(
    ! [X8] :
      ( r2_hidden(sK4(X8,k4_subset_1(sK0,sK1,sK1),X8),sK0)
      | k3_tarski(k2_enumset1(X8,X8,X8,sK1)) = X8 ) ),
    inference(forward_demodulation,[],[f648,f451])).

fof(f648,plain,(
    ! [X8] :
      ( k3_tarski(k2_enumset1(X8,X8,X8,sK1)) = X8
      | r2_hidden(sK4(X8,k4_subset_1(sK0,sK1,sK1),X8),k4_subset_1(sK0,sK0,sK0)) ) ),
    inference(forward_demodulation,[],[f438,f510])).

fof(f438,plain,(
    ! [X8] :
      ( k3_tarski(k2_enumset1(X8,X8,X8,k4_subset_1(sK0,sK1,sK1))) = X8
      | r2_hidden(sK4(X8,k4_subset_1(sK0,sK1,sK1),X8),k4_subset_1(sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f373,f383])).

fof(f383,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_subset_1(sK0,sK1,sK1))
      | r2_hidden(X0,k4_subset_1(sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f317,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f317,plain,(
    r1_tarski(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( r1_tarski(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK0,sK0))
    | r1_tarski(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK0,sK0)) ),
    inference(resolution,[],[f291,f166])).

fof(f166,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k4_subset_1(sK0,sK1,sK1),X0),sK0)
      | r1_tarski(k4_subset_1(sK0,sK1,sK1),X0) ) ),
    inference(resolution,[],[f141,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f32,f70])).

fof(f70,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f68,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f68,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f64,f22])).

fof(f22,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f64,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f31,f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f141,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k4_subset_1(sK0,sK1,sK1),X1),sK1)
      | r1_tarski(k4_subset_1(sK0,sK1,sK1),X1) ) ),
    inference(resolution,[],[f138,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_subset_1(sK0,sK1,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_subset_1(sK0,sK1,sK1))
      | r2_hidden(X0,sK1)
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f61,f131])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f291,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,k4_subset_1(X1,X1,X1)),X1)
      | r1_tarski(X0,k4_subset_1(X1,X1,X1)) ) ),
    inference(resolution,[],[f287,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f287,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,k4_subset_1(X4,X4,X4))
      | ~ r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f60,f258])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f674,plain,
    ( sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK4(sK0,sK1,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f671])).

fof(f671,plain,
    ( sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK4(sK0,sK1,sK0),sK0)
    | sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(resolution,[],[f650,f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (3592)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (3584)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (3587)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (3585)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (3580)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (3600)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (3602)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (3579)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (3594)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (3582)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (3583)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (3586)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (3605)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (3596)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (3581)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (3604)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (3606)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (3607)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (3599)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (3603)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (3598)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (3608)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.55  % (3597)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.55  % (3601)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.46/0.55  % (3588)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.55  % (3601)Refutation not found, incomplete strategy% (3601)------------------------------
% 1.46/0.55  % (3601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (3601)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (3601)Memory used [KB]: 10746
% 1.46/0.55  % (3601)Time elapsed: 0.151 s
% 1.46/0.55  % (3601)------------------------------
% 1.46/0.55  % (3601)------------------------------
% 1.46/0.55  % (3595)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.55  % (3590)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.55  % (3589)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.55  % (3593)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.55  % (3591)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.46/0.55  % (3590)Refutation not found, incomplete strategy% (3590)------------------------------
% 1.46/0.55  % (3590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (3590)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (3590)Memory used [KB]: 10618
% 1.46/0.55  % (3590)Time elapsed: 0.151 s
% 1.46/0.55  % (3590)------------------------------
% 1.46/0.55  % (3590)------------------------------
% 1.46/0.55  % (3596)Refutation not found, incomplete strategy% (3596)------------------------------
% 1.46/0.55  % (3596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (3596)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (3596)Memory used [KB]: 10618
% 1.46/0.55  % (3596)Time elapsed: 0.146 s
% 1.46/0.55  % (3596)------------------------------
% 1.46/0.55  % (3596)------------------------------
% 1.62/0.56  % (3589)Refutation not found, incomplete strategy% (3589)------------------------------
% 1.62/0.56  % (3589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.56  % (3589)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.56  
% 1.62/0.56  % (3589)Memory used [KB]: 10618
% 1.62/0.56  % (3589)Time elapsed: 0.144 s
% 1.62/0.56  % (3589)------------------------------
% 1.62/0.56  % (3589)------------------------------
% 1.62/0.58  % (3585)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  fof(f677,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(subsumption_resolution,[],[f676,f277])).
% 1.62/0.58  fof(f277,plain,(
% 1.62/0.58    sK0 != k4_subset_1(sK0,sK0,sK1)),
% 1.62/0.58    inference(superposition,[],[f62,f268])).
% 1.62/0.58  fof(f268,plain,(
% 1.62/0.58    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 1.62/0.58    inference(forward_demodulation,[],[f261,f132])).
% 1.62/0.58  fof(f132,plain,(
% 1.62/0.58    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.62/0.58    inference(resolution,[],[f127,f63])).
% 1.62/0.58  fof(f63,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(forward_demodulation,[],[f24,f23])).
% 1.62/0.58  fof(f23,plain,(
% 1.62/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f9,axiom,(
% 1.62/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f10])).
% 1.62/0.58  fof(f10,axiom,(
% 1.62/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.62/0.58  fof(f127,plain,(
% 1.62/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1))) )),
% 1.62/0.58    inference(resolution,[],[f50,f20])).
% 1.62/0.58  fof(f20,plain,(
% 1.62/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.58    inference(cnf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,plain,(
% 1.62/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f14])).
% 1.62/0.58  fof(f14,negated_conjecture,(
% 1.62/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.62/0.58    inference(negated_conjecture,[],[f13])).
% 1.62/0.58  fof(f13,conjecture,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 1.62/0.58  fof(f50,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f40,f48])).
% 1.62/0.58  fof(f48,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f26,f47])).
% 1.62/0.58  fof(f47,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f27,f39])).
% 1.62/0.58  fof(f39,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f5])).
% 1.62/0.58  fof(f5,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.62/0.58  fof(f26,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f7])).
% 1.62/0.58  fof(f7,axiom,(
% 1.62/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.62/0.58  fof(f40,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f19])).
% 1.62/0.58  fof(f19,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.58    inference(flattening,[],[f18])).
% 1.62/0.58  fof(f18,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.62/0.58    inference(ennf_transformation,[],[f12])).
% 1.62/0.58  fof(f12,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.62/0.58  fof(f261,plain,(
% 1.62/0.58    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.62/0.58    inference(superposition,[],[f257,f49])).
% 1.62/0.58  fof(f49,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f25,f48,f48])).
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.62/0.58  fof(f257,plain,(
% 1.62/0.58    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0))),
% 1.62/0.58    inference(resolution,[],[f128,f20])).
% 1.62/0.58  fof(f128,plain,(
% 1.62/0.58    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X2,X1,X2)) )),
% 1.62/0.58    inference(resolution,[],[f50,f63])).
% 1.62/0.58  fof(f62,plain,(
% 1.62/0.58    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 1.62/0.58    inference(backward_demodulation,[],[f21,f23])).
% 1.62/0.58  fof(f21,plain,(
% 1.62/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.62/0.58    inference(cnf_transformation,[],[f15])).
% 1.62/0.58  fof(f676,plain,(
% 1.62/0.58    sK0 = k4_subset_1(sK0,sK0,sK1)),
% 1.62/0.58    inference(backward_demodulation,[],[f132,f675])).
% 1.62/0.58  fof(f675,plain,(
% 1.62/0.58    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.62/0.58    inference(subsumption_resolution,[],[f674,f650])).
% 1.62/0.58  fof(f650,plain,(
% 1.62/0.58    ( ! [X8] : (r2_hidden(sK4(X8,sK1,X8),sK0) | k3_tarski(k2_enumset1(X8,X8,X8,sK1)) = X8) )),
% 1.62/0.58    inference(forward_demodulation,[],[f649,f510])).
% 1.62/0.58  fof(f510,plain,(
% 1.62/0.58    sK1 = k4_subset_1(sK0,sK1,sK1)),
% 1.62/0.58    inference(backward_demodulation,[],[f285,f451])).
% 1.62/0.58  fof(f451,plain,(
% 1.62/0.58    ( ! [X0] : (k4_subset_1(X0,X0,X0) = X0) )),
% 1.62/0.58    inference(backward_demodulation,[],[f258,f450])).
% 1.62/0.58  fof(f450,plain,(
% 1.62/0.58    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f449,f54])).
% 1.62/0.58  fof(f54,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 1.62/0.58    inference(definition_unfolding,[],[f43,f48])).
% 1.62/0.58  fof(f43,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 1.62/0.58    inference(cnf_transformation,[],[f3])).
% 1.62/0.58  fof(f3,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.62/0.58  fof(f449,plain,(
% 1.62/0.58    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 | ~r2_hidden(sK4(X0,X0,X0),X0)) )),
% 1.62/0.58    inference(duplicate_literal_removal,[],[f433])).
% 1.62/0.58  fof(f433,plain,(
% 1.62/0.58    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 | ~r2_hidden(sK4(X0,X0,X0),X0) | k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.62/0.58    inference(resolution,[],[f373,f56])).
% 1.62/0.58  fof(f56,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 1.62/0.58    inference(definition_unfolding,[],[f41,f48])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 1.62/0.58    inference(cnf_transformation,[],[f3])).
% 1.62/0.58  fof(f373,plain,(
% 1.62/0.58    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X3) | k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X2) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f365,f56])).
% 1.62/0.58  fof(f365,plain,(
% 1.62/0.58    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X2) | r2_hidden(sK4(X2,X3,X2),X3) | k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X2) )),
% 1.62/0.58    inference(factoring,[],[f54])).
% 1.62/0.58  fof(f258,plain,(
% 1.62/0.58    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0)) )),
% 1.62/0.58    inference(resolution,[],[f128,f63])).
% 1.62/0.58  fof(f285,plain,(
% 1.62/0.58    k4_subset_1(sK0,sK1,sK1) = k4_subset_1(sK1,sK1,sK1)),
% 1.62/0.58    inference(superposition,[],[f258,f131])).
% 1.62/0.58  fof(f131,plain,(
% 1.62/0.58    k4_subset_1(sK0,sK1,sK1) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.62/0.58    inference(resolution,[],[f127,f20])).
% 1.62/0.58  fof(f649,plain,(
% 1.62/0.58    ( ! [X8] : (r2_hidden(sK4(X8,k4_subset_1(sK0,sK1,sK1),X8),sK0) | k3_tarski(k2_enumset1(X8,X8,X8,sK1)) = X8) )),
% 1.62/0.58    inference(forward_demodulation,[],[f648,f451])).
% 1.62/0.58  fof(f648,plain,(
% 1.62/0.58    ( ! [X8] : (k3_tarski(k2_enumset1(X8,X8,X8,sK1)) = X8 | r2_hidden(sK4(X8,k4_subset_1(sK0,sK1,sK1),X8),k4_subset_1(sK0,sK0,sK0))) )),
% 1.62/0.58    inference(forward_demodulation,[],[f438,f510])).
% 1.62/0.58  fof(f438,plain,(
% 1.62/0.58    ( ! [X8] : (k3_tarski(k2_enumset1(X8,X8,X8,k4_subset_1(sK0,sK1,sK1))) = X8 | r2_hidden(sK4(X8,k4_subset_1(sK0,sK1,sK1),X8),k4_subset_1(sK0,sK0,sK0))) )),
% 1.62/0.58    inference(resolution,[],[f373,f383])).
% 1.62/0.58  fof(f383,plain,(
% 1.62/0.58    ( ! [X0] : (~r2_hidden(X0,k4_subset_1(sK0,sK1,sK1)) | r2_hidden(X0,k4_subset_1(sK0,sK0,sK0))) )),
% 1.62/0.58    inference(resolution,[],[f317,f32])).
% 1.62/0.58  fof(f32,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,plain,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f2])).
% 1.62/0.58  fof(f2,axiom,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.58  fof(f317,plain,(
% 1.62/0.58    r1_tarski(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK0,sK0))),
% 1.62/0.58    inference(duplicate_literal_removal,[],[f313])).
% 1.62/0.58  fof(f313,plain,(
% 1.62/0.58    r1_tarski(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK0,sK0)) | r1_tarski(k4_subset_1(sK0,sK1,sK1),k4_subset_1(sK0,sK0,sK0))),
% 1.62/0.58    inference(resolution,[],[f291,f166])).
% 1.62/0.58  fof(f166,plain,(
% 1.62/0.58    ( ! [X0] : (r2_hidden(sK2(k4_subset_1(sK0,sK1,sK1),X0),sK0) | r1_tarski(k4_subset_1(sK0,sK1,sK1),X0)) )),
% 1.62/0.58    inference(resolution,[],[f141,f77])).
% 1.62/0.58  fof(f77,plain,(
% 1.62/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 1.62/0.58    inference(resolution,[],[f32,f70])).
% 1.62/0.58  fof(f70,plain,(
% 1.62/0.58    r1_tarski(sK1,sK0)),
% 1.62/0.58    inference(resolution,[],[f68,f57])).
% 1.62/0.58  fof(f57,plain,(
% 1.62/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.62/0.58    inference(equality_resolution,[],[f36])).
% 1.62/0.58  fof(f36,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.62/0.58    inference(cnf_transformation,[],[f6])).
% 1.62/0.58  fof(f6,axiom,(
% 1.62/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.62/0.58  fof(f68,plain,(
% 1.62/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.58    inference(subsumption_resolution,[],[f64,f22])).
% 1.62/0.58  fof(f22,plain,(
% 1.62/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f11])).
% 1.62/0.58  fof(f11,axiom,(
% 1.62/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.62/0.58  fof(f64,plain,(
% 1.62/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.62/0.58    inference(resolution,[],[f31,f20])).
% 1.62/0.58  fof(f31,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f16])).
% 1.62/0.58  fof(f16,plain,(
% 1.62/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f8])).
% 1.62/0.58  fof(f8,axiom,(
% 1.62/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.62/0.58  fof(f141,plain,(
% 1.62/0.58    ( ! [X1] : (r2_hidden(sK2(k4_subset_1(sK0,sK1,sK1),X1),sK1) | r1_tarski(k4_subset_1(sK0,sK1,sK1),X1)) )),
% 1.62/0.58    inference(resolution,[],[f138,f33])).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f138,plain,(
% 1.62/0.58    ( ! [X0] : (~r2_hidden(X0,k4_subset_1(sK0,sK1,sK1)) | r2_hidden(X0,sK1)) )),
% 1.62/0.58    inference(duplicate_literal_removal,[],[f135])).
% 1.62/0.58  fof(f135,plain,(
% 1.62/0.58    ( ! [X0] : (~r2_hidden(X0,k4_subset_1(sK0,sK1,sK1)) | r2_hidden(X0,sK1) | r2_hidden(X0,sK1)) )),
% 1.62/0.58    inference(superposition,[],[f61,f131])).
% 1.62/0.58  fof(f61,plain,(
% 1.62/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 1.62/0.58    inference(equality_resolution,[],[f53])).
% 1.62/0.58  fof(f53,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.62/0.58    inference(definition_unfolding,[],[f44,f48])).
% 1.62/0.58  fof(f44,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.62/0.58    inference(cnf_transformation,[],[f3])).
% 1.62/0.58  fof(f291,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r2_hidden(sK2(X0,k4_subset_1(X1,X1,X1)),X1) | r1_tarski(X0,k4_subset_1(X1,X1,X1))) )),
% 1.62/0.58    inference(resolution,[],[f287,f34])).
% 1.62/0.58  fof(f34,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f287,plain,(
% 1.62/0.58    ( ! [X4,X5] : (r2_hidden(X5,k4_subset_1(X4,X4,X4)) | ~r2_hidden(X5,X4)) )),
% 1.62/0.58    inference(superposition,[],[f60,f258])).
% 1.62/0.58  fof(f60,plain,(
% 1.62/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~r2_hidden(X3,X0)) )),
% 1.62/0.58    inference(equality_resolution,[],[f52])).
% 1.62/0.58  fof(f52,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.62/0.58    inference(definition_unfolding,[],[f45,f48])).
% 1.62/0.58  fof(f45,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.62/0.58    inference(cnf_transformation,[],[f3])).
% 1.62/0.58  fof(f674,plain,(
% 1.62/0.58    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(sK0,sK1,sK0),sK0)),
% 1.62/0.58    inference(duplicate_literal_removal,[],[f671])).
% 1.62/0.58  fof(f671,plain,(
% 1.62/0.58    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(sK0,sK1,sK0),sK0) | sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.62/0.58    inference(resolution,[],[f650,f56])).
% 1.62/0.58  % SZS output end Proof for theBenchmark
% 1.62/0.58  % (3585)------------------------------
% 1.62/0.58  % (3585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (3585)Termination reason: Refutation
% 1.62/0.58  
% 1.62/0.58  % (3585)Memory used [KB]: 6780
% 1.62/0.58  % (3585)Time elapsed: 0.179 s
% 1.62/0.58  % (3585)------------------------------
% 1.62/0.58  % (3585)------------------------------
% 1.62/0.58  % (3578)Success in time 0.226 s
%------------------------------------------------------------------------------
